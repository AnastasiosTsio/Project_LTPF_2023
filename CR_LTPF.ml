(*
Auteurs : 
- Alexis NOEL 
- Noah KOHRS
- Anastasios TSIOMPANIDIS
*)

type avar = int ;;  

type bexp =
  | Bcst of bool
  | Ava of avar
  | And of bexp * bexp
  | Or of bexp * bexp
  | Not of bexp
;;

type winstr =
  | Skip 
  | Assign of avar * bexp
  | Seq of winstr * winstr
  | If of avar * winstr * winstr
  | While of avar * winstr
;;

let rec bexpPrinter : (bexp -> string) = fun exp ->
  match exp with
  | Bcst true -> "true"
  | Bcst false -> "false"
  | And (left, right) -> "(" ^ (bexpPrinter left) ^ " || " ^ (bexpPrinter right) ^ ")"
  | Or (left, right) -> "(" ^ (bexpPrinter left) ^ " && " ^ (bexpPrinter right) ^ ")"
  | Not (exp) -> "!(" ^ (bexpPrinter exp) ^ ")"
  | Ava i -> match i with
    | 0 -> "a"
    | 1 -> "b"
    | 2 -> "c"
    | 3 -> "d"
    | _ -> "error"
;;

(* Fonction pour faciliter le testing *)
let winstrPrinter : (winstr -> string) = fun instr ->
  let rec aux : (winstr -> string) = fun instr ->
    match instr with
    | Skip -> "skip"
    | Assign (left, right) -> (bexpPrinter (Ava left)) ^ " := " ^ (bexpPrinter right)
    | Seq (left, right) -> (aux left) ^ ";\n" ^ (aux right)
    | If (cond, if_then, if_else) -> "if " ^ (bexpPrinter (Ava cond)) ^ " then {\n" ^ (aux if_then) ^ "\n} else {\n" ^ (aux if_else) ^ "\n}"
    | While (cond, body) -> "while (" ^ (bexpPrinter (Ava cond)) ^ ") do {\n" ^ (aux body) ^ "\n}"
  in aux instr
;;

(*
Exercice 1.1.1
Définir une hiérarchie de types OCaml permettant de représenter tous les programmes admis par la description ci-dessus.

Dans un premier temps on va économiser la phase traditionnelle d'analyse lexicale. Pour cela on écrit
les mots-clés du langage sur un seul caractère, on délimite le corps des if et des while par des accolades et
on se dispense du mot-clé else (quitte à laisser un programme vide pour le second bloc du if).
Ainsi, notre programme exemple du début de l'énoncé s'écrit :
a:=1;
b:=1;
c:=1;
w(a){
i(c){
c:=0;
a:=b
}{
b:=0;
c:=a
}
}
On a ici conservé les tabulations et les retours à la ligne pour que le programme reste lisible, mais si on s'en
dispense, notre programme s'écrit :
a:=1;b:=1;c:=1;w(a){i(c){c:=0;a:=b}{b:=0;c:=a}}

--------------------------------------------------------------------------------------

Grammaire
  VAL   ::= '0' | '1'
  VAR   ::= 'a' | 'b' | 'c' | 'd'
  EXPR  ::= VAL | VAR
  SKIP  ::= ε
  WHILE ::= 'w' '(' VAR ')' '{' BLOCK '}'
  ASSIG ::= VAR ':=' EXPR
  IF    ::= 'i' '(' VAR ')' '{' BLOCK '}' '{' BLOCK '}'
  SEQ   ::= (';' INSTR SEQ) | ε
  INSTR ::= ( WHILE | IF | ASSIGN | SKIP )
  BLOCK ::= INSTR SEQ

--------------------------------------------------------------------------------------

Exercice 1.4
  C ::= '0' | '1'
  V ::= 'a' | 'b' | 'c' | 'd'
  A ::= C | V
  E ::= T E'
  E'::= '+' T E' | ε
  T ::= F T'
  T'::= '.' F T' | ε
  F ::= '!' F | A | '(' E ')'

  Pour implémenter cette obtenir le language WHILEb à 
  partir de WHILEb~~ et de ce language d'expression, il suffit de remplacer
  EXPR de la grammaire WHILEb~~ tel que :
  EXPR :== E

  C'est ce que nous ferons dans la suite.

*)

(*-------------------------------------------------------------------------------*)
(*Anacomb.ml*)

let list_of_string s =
  let n = String.length s in
  let rec boucle i =
    if i = n then [] else s.[i] :: boucle (i+1)
  in boucle 0
;;
(* Le type des aspirateurs (fonctions qui aspirent le préfixe d'une liste) *)
type 'term analist = 'term list -> 'term list;;

exception Echec;;

(* terminal constant *)
let terminal (c : 't) : 't analist = function
  | x :: l when x = c -> l
  | _ -> raise Echec
;;
(* terminal conditionnel *)
let terminal_cond (p : 'term -> bool) : 'term analist = function
  | x :: l when p x -> l
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
(* Choix entre a1 ou a2 *)
let (-|) (a1 : 'term analist) (a2 : 'term analist) : 'term analist =
  fun l -> try a1 l with Echec -> a2 l
;;
(* Répétition (étoile de Kleene) *)
(* Grammaire :  A* ::=  A A* | ε *)
let rec star (a : 'term analist) : 'term analist = fun l -> l |>
                                                            ( a --> star a ) -| epsilon
;;
(* ------------------------------------------------------------ *)
(* Combinateurs d'analyseurs
   avec calcul supplémentaire, ex. d'un AST *)
(* ------------------------------------------------------------ *)

(* Le type des aspirateurs qui, en plus, rendent un résultat *)
type ('res, 'term) ranalist = 'term list -> 'res * 'term list;;

(* Un epsilon informatif *)
let epsilon_res (info : 'res) : ('res, 'term) ranalist =
  fun l -> (info, l)
;;
(* Terminal conditionnel avec résultat *)
(* [f] ne retourne pas un booléen mais un résultat optionnel *)
let terminal_res (f : 'term -> 'res option) : ('res, 'term) ranalist =
  fun l -> match l with
    | x :: l -> (match f x with Some y -> y, l | None -> raise Echec)
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

(* fin Anacomb.ml *)
(*------------------------------------------------------------------*)

(* A partir d'ici, nous ajoutons nous même quelques outils qui seront utiles pour la suite. *)

(* L'opérateur (+->) qui prend a1 rendant un resultat suivi de a2 sans resultat.  *)
let (+->) (a1 : ('res, 'term) ranalist) (a2 : 'term analist) :
  ('res, 'term) ranalist =
  fun l -> let r1,l1 = a1 l in (r1,a2 l1)
;;

(* Terminal qui prend toute une chaine de caractère d'un coup. *)
let terminal_string (s : string) : char analist =
  let rec aux : (char list -> char analist) = fun l ->
    match l with
    | [] -> epsilon
    | c :: queue -> (terminal c) --> (aux queue)
  in aux (list_of_string s)
;;

(* Exercice 2.1.1 TEST en ANALIST *)

(* Rappel Grammaire
   VAL   ::= '0' | '1'
   VAR   ::= 'a' | 'b' | 'c' | 'd'
   EXPR  ::= VAL | VAR
   SKIP  ::= ε
   WHILE ::= 'w' '(' VAR ')' '{' BLOCK '}'
   ASSIG ::= VAR ':=' EXPR
   IF    ::= 'i' '(' VAR ')' '{' BLOCK '}' '{' BLOCK '}'
   SEQ   ::= (';' INSTR SEQ) | ε
   INSTR ::= ( WHILE | IF | ASSIGN | SKIP )
   BLOCK ::= INSTR SEQ
*)

(* VERSION ANALIST *)

let pVAL = terminal '0' -| terminal '1';;
let pVAR = terminal 'a' -| terminal 'b' -| terminal 'c' -| terminal 'd';;
let pEXPR = pVAL -| pVAR;;

let pSKIP = epsilon;;
let pASSIG = (pVAR --> terminal ':' --> terminal '=' --> pEXPR);;

let rec pINSTR = fun l ->
  (( pWHILE -| pIF -| pASSIG -| pSKIP ) --> pSEQ ) l

and pWHILE = fun l -> ((terminal 'w') --> 
                       (terminal '(') --> pVAR --> (terminal ')') 
                       --> (terminal '{') --> pBLOCK --> (terminal '}')) l

and pIF = fun l -> (terminal 'i' --> 
                    terminal '(' --> pVAR --> terminal ')' 
                    --> terminal '{' --> pBLOCK --> terminal '}' 
                    --> terminal '{' --> pBLOCK --> terminal '}') l

and pSEQ = fun l -> ((terminal ';' --> pINSTR --> pSEQ ) -| epsilon) l

and pBLOCK = fun l -> (pINSTR --> pSEQ) l  
;; 

let pWHILEb = pINSTR;;

(* Exercice 2.1.2 [Pour ANALIST] *)
(* Tests qui vérifient la validité *)
let test_stp= pWHILEb (list_of_string "a:=1;b:=1;c:=1;w(a){i(c){c:=0;a:=b}{b:=0;c:=a}}");;

let test_stp2= pWHILEb (list_of_string "i(a){}{}");;

(* Tests qui verifient l'invalidité *)

(* Variable inexistante *)
let test_stp3= pWHILEb (list_of_string "a:=e;");;

(* Affection de constante *)
let test_stp4= pWHILEb (list_of_string "1:=1");;

(* If sans else *)
let test_stp5= pWHILEb (list_of_string "i(c){b:=0;c:=a}");;


(* Exercice 2.1.1 + 2.1.3 + 2.1.4 *)
(* VERSION RANALIST *)
(* Remarque :
  On implémentera dès maintenant les bexp du 2.1.3 ainsi que la suppression des vides du 2.1.4 afin d'éviter les répétitions.
*)

let valOption : (char->bexp option) = fun c -> 
  match c with 
  | '0' -> Some(Bcst false)
  | '1' -> Some(Bcst true)
  |  _  -> None
;;

let varOption : (char -> avar option) = fun c -> 
  match c with 
  | 'a' -> Some(0)
  | 'b' -> Some(1)
  | 'c' -> Some(2)
  | 'd' -> Some(3)
  |  _  -> None
;;

(* Rappel Grammaires :
   ----- BEXP ----- (début E)
   VAL  ::= '0' | '1'
   VAR  ::= 'a' | 'b' | 'c' | 'd'
   A    ::= C | V
   E    ::= T E'
   E'   ::= '+' T E' | ε
   T    ::= F T'
   T'   ::= '.' F T' | ε
   F    ::= '!' F | A | '(' E ')'

   ----- INSTR ----- (début BLOCK)

   EXPR  ::= E
   SKIP  ::= ε
   WHILE ::= 'w' '(' VAR ')' '{' BLOCK '}'
   ASSIG ::= VAR ':=' EXPR
   IF    ::= 'i' '(' VAR ')' '{' BLOCK '}' '{' BLOCK '}'
   SEQ   ::= (';' INSTR SEQ) | ε
   INSTR ::= ( WHILE | IF | ASSIGN | SKIP )
   BLOCK ::= INSTR SEQ 
*)

(* Grammaire des expressions booléennes ~ 2.1.3 *)
let rVAL  : ((bexp, char) ranalist) = terminal_res valOption;;
let rVAR  : ((avar, char) ranalist) = terminal_res varOption;;
let rA = rVAL +| (rVAR ++> fun var -> epsilon_res (Ava var));;

let rec rE = fun l ->
  (rT ++> fun left -> rE' left) l

and rE' = fun left l ->
  (
    (terminal '+' -+> rT ++> fun right -> rE' (Or(left,right)))
    +| 
    epsilon_res left
  ) l

and rT = fun l ->
  (rF ++> fun left -> rT' left) l

and rT' = fun left l ->
  (
    (terminal '.' -+> rF ++> fun right -> rT' (And(left,right)))
    +| 
    epsilon_res left
  ) l

and rF = fun l ->
  (
    (terminal '!' -+> rF ++> fun right -> epsilon_res (Not(right)))
    +|
    rA
    +|
    (terminal '(' -+> rE +-> terminal ')' )
  ) l
;;

(* Grammaire des instructions ~ 2.1.1*)

let rEXPR = rE ;;

let rec rASSIG : ((winstr, char) ranalist) = fun l ->
  (rVAR +-> terminal ':' +-> terminal '=' ++>
  fun (left : avar) : (((winstr, char) ranalist)) ->
    (rEXPR ++> fun (right : bexp) -> epsilon_res (Assign(left,right)))
  ) l
;;

let rSKIP = fun l ->
  epsilon_res Skip l
;;

let rec rBLOCK : ((winstr, char) ranalist) = fun l ->
  (
  (rINSTR ++> 
    fun left -> rSEQ left)
  ) l

and rINSTR : ((winstr, char) ranalist) = fun l ->
  (
    rWHILE +| rIF +| rASSIG +| rSKIP
  ) l
and rWHILE : ((winstr, char) ranalist) = fun l ->
  (terminal 'w' --> terminal '(' -+> rVAR +-> terminal ')' +-> terminal '{' ++>
    fun left -> rBLOCK ++> fun right -> epsilon_res (While(left,right)) 
  +-> terminal '}'
  ) l
and rIF : ((winstr, char) ranalist) = fun l ->
  (terminal 'i' --> terminal '(' -+> rVAR +-> terminal ')' +-> terminal '{' ++>
    fun cond -> rBLOCK +-> terminal '}' +-> terminal '{' ++> 
    fun if_then -> rBLOCK +-> terminal '}' ++> fun if_else -> epsilon_res (If(cond,if_then,if_else))
  ) l
and rSEQ : winstr->((winstr, char) ranalist) = fun left l ->
  (
  (terminal ';' -+> rINSTR ++> 
    fun instr -> rSEQ (Seq(left,instr))
  ) 
  +| epsilon_res left
  ) l
;;

(* Système de supression des caractères blancs ~ Exercice 2.1.4 *)

(*
Nous avons proposé deux solutions : 
  - Une première solution mettant en place un filtre qui va parser une première fois l'expression en enlevant
tout les espaces et les retours à la ligne
  - Une seconde solution, utilisant des terminaux récursifs, qui suppriment les espaces et les entrées à la ligne.
Pour mettre en place cette deuxième solution, il suffit de emplacer tous les terminaux par les terminaux sup dans notre
*)

(*Version utilisant un pré-filtrage*)
let rec filter : (char list -> char list -> char list) = fun code blankChars ->
  let rec auxFilter : (char -> char list -> char list) = fun c code ->
    match code with
    | [] -> []
    | e::queue -> 
      if (e = c) then (auxFilter c queue)
      else [e] @ (auxFilter c queue)
  in
  match blankChars with
  | [] -> code 
  | c::queue -> filter (auxFilter c code) queue
;;

let rWHILEb : (string -> winstr*char list) = fun l ->
  rBLOCK (filter (list_of_string l) (list_of_string " \t\r")) 
;;


let check : (winstr * (char list)) -> string = 
  fun (instr, l) ->
  match l with
  | [] -> winstrPrinter instr
  | _ -> "Erreur"  
;;

let test_WHILEb : (string -> unit) = fun s -> 
  print_string ("\n\n" ^ (check (rWHILEb s)) ^ "\n\n")
;;

(* Version utilisant Terminal_SUP *)
let rec terminal_SUP c l =
  l
  |> terminal ' ' --> terminal_SUP c
     -| (terminal '\n' --> terminal_SUP c)
     -| terminal c

let rec terminal_cond_SUP p l =
  l
  |> terminal ' ' --> terminal_cond_SUP p
     -| (terminal '\n' --> terminal_cond_SUP p)
     -| terminal_cond p

let rec epsilon_SUP l =
  l
  |> terminal ' ' --> epsilon_SUP -| (terminal '\n' --> epsilon_SUP) -| epsilon
;;

(* Tests qui vérifient la validité *)

filter (list_of_string "a a a     \taaaa") (list_of_string " \t");;

test_WHILEb "a:=1";;

test_WHILEb "a:=1;b:=1;c:=1;w(a){i(c){c:=0;a:=b}{b:=0;c:=a}}";;

test_WHILEb "w(a){}";;

test_WHILEb "i(a){}{}";;

rEXPR (list_of_string "(a+b)");;
rEXPR (list_of_string "((a))");;
rINSTR (list_of_string "(a.b+c)+1");;

rWHILEb "a:=((a.b+c)+1)";;

test_WHILEb "a:=((a .   b+c)+0)";;
test_WHILEb "a:=(0.0.0.1+1.0.0.0)";;

(* Tests qui verifient l'invalidité *)
test_WHILEb "a:=e;";;

test_WHILEb "1:=1";;

test_WHILEb "i(c){b:=0;c:=a}";;

type state = bool list;;

let rec getValue : (state -> int -> bool) = fun s i ->
  match s with
  | a :: l1 -> if (i = 0) then a else getValue l1 (i-1)
  | [] -> false
;;


let  rec update (s:state) (v:int) (n:bool): state =
  match v,s with
  | 0 , h :: d -> n :: d
  | 0 , []     -> n :: []
  | v1, h :: d -> h :: (update d (v1-1) n)
  | v1, []     -> false :: (update [] (v1-1) n)
;;

let rec evalBooleanExpression : (state -> bexp -> bool) = fun s exp ->
  match exp with
  | Bcst b            -> b
  | Ava i             -> (getValue s i)
  | And (left, right) -> (evalBooleanExpression s left) && (evalBooleanExpression s right)
  | Or (left, right)  -> (evalBooleanExpression s left) || (evalBooleanExpression s right)
  | Not (exp)         -> not (evalBooleanExpression s exp)
;;

let evalAssign : (state -> avar -> bexp -> state) = fun s left right -> update s left (evalBooleanExpression s right)
;;

let rec evalProgram : (state -> winstr -> state) = fun s instr ->
  match instr with 
  | Skip -> s
  | Assign (left, right) -> evalAssign s left right
  | Seq (left, right) -> let s = (evalProgram s left) in (evalProgram s right)
  | If (cond, if_then, if_else) -> 
      if (evalBooleanExpression s (Ava cond)) 
        then (evalProgram s if_then)
        else (evalProgram s if_else)
  | While (cond, while_do) -> 
      if (evalBooleanExpression s (Ava cond)) then let s = (evalProgram s while_do) in (evalProgram s instr)
      else s
    ;;

let toAST : (string -> winstr) = fun s ->
  let (ast,_) = rWHILEb s in ast
;; 

let evaluate = evalProgram [false;false;false;false] ;; 

let test_eval1 = evaluate (Assign (0, Bcst true));; (*[true;true,false,falsee]*)
let test_eval2 = evaluate (toAST "b := 1");; (*[false;true,false,falsee]*)
let test_eval3 = evaluate (toAST " a := 1; w(a) { i(d) { a:= 0} { d:=1 } }; b: = 1");; (*[false;true;false;true]*)
let test_eval4 = evaluate (toAST "");;(*[false;false;false;false]*)
let test_eval5 = evaluate (toAST "a := 1; b := 1; c := 1; w(a){i(c){c := 0; a := b}{b := 0; c := a}}");; (*[false;false;false;false]*)

(* Question 3.1 *)

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

(* Tokens pour le lexer *)
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

(* Terminal string sortant le token *)
let terminal_lex : (string -> (token) -> (token, char) ranalist) =
  fun str tok -> terminal_string str -+> epsilon_res tok
;;

(* Terminal string sortant le token si la suite n'est pas alphanumerique *)
let terminal_key_lex : (string -> (token) -> (token, char) ranalist) =
  fun s tok l -> let (newToken, newList) =  (terminal_lex s tok l) 
  in 
  match newList with
  | x :: _ when (is_alpha_numeric x) -> raise Echec
  | _ -> (newToken, newList)
;;

(* Terminal pour *)
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
  let rec collect_chars acc = function
    | [] -> (acc, [])
    | x :: xs when is_alpha_numeric x -> collect_chars (acc ^ Char.escaped x) xs
    | l -> (acc, l)
  in
  fun l -> match l with
    | x :: xs when is_letter x -> let (acc, l) = collect_chars (Char.escaped x) xs in
                                  (LexVariable acc, l)
    | _ -> raise Echec
;;

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

let lexer : (token list, char) ranalist = star_list allPaths;;

(* Test *)

lexer (list_of_string "if(harry == true) then !1 else false ");;

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
  fun l -> match l with
    | (LexBoolean b) :: l -> (Bcst b, l)
    | _ -> raise Echec
;;

let rVAR : (variable, token) ranalist =
  fun l -> match l with
    | (LexVariable v) :: l -> (v, l)
    | _ -> raise Echec
;;

let rA : (bexp, token) ranalist = rVAL +| (rVAR ++> fun v -> epsilon_res (Ava v));;

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

let myLangToAST : (string -> winstr*token list) = fun l ->
  let (toks, _) = (lexer (list_of_string l)) in
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
harry := 1;
bouteille := 1;
if (harry && bouteille == true) 
  then{bouteille := 1} 
  else{bouteille := false};
"
;;

(* Question 3.3 *)

(*  
A partir d'ici, toute les fonctionalités d'anacomb ont été 
réimplémentées pour fonctionner avec des listes paresseuses. 
*)

type variable = string;;

type 'a inflist = unit -> 'a contentsil
and 'a contentsil = Cons of 'a * 'a inflist
;;

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

(* Lexing *)

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

lexer (inflist_of_string "if(harry == true) then !1 else false ");;

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
if (harry && bouteille == true) 
  then {bouteille := 1} 
  else{bouteille := false}
"
;;
