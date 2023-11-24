

type bexp = 
  | Bcst of bool
  | Ava of int
  | And of bexp * bexp
  | Or of bexp * bexp
  | Not of bexp
;;

type winstr =
  | Skip 
  | Assign of bexp * bexp
  | Seq of winstr * winstr
  | If of bexp * winstr * winstr
  | While of bexp * winstr
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
    | Assign (left, right) -> (bexpPrinter left) ^ " := " ^ (bexpPrinter right)
    | Seq (left, right) -> (aux left) ^ ";\n" ^ (aux right)
    | If (cond, if_then, if_else) -> "if " ^ (bexpPrinter cond) ^ " then {\n" ^ (aux if_then) ^ "\n} else {\n" ^ (aux if_else) ^ "\n}"
    | While (cond, body) -> "while (" ^ (bexpPrinter cond) ^ ") do {\n" ^ (aux body) ^ "\n}"
  in aux instr
;;

(*
Exercice 1.1.1 Définir une hiérarchie de types OCaml permettant de représenter tous les programmes admis par la description ci-dessus.
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

*)

(* Grammaire
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



(* Exercice 1.4
   Version 1 :
   C ::= '0' | '1'
   V ::= 'a' | 'b' | 'c' | 'd'
   A ::= C | V
   E ::= T '+' E | T
   T ::= F '.' T | F
   F ::= '!' F | A | '(' E ')'
   D ::= A T | A E | F D
   =================================
   Version 2 (suivant mzthode plus classique):
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
*)


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
(*
Nous ajoutons nous même : 
a1 rendant un résultat suivi de a2 sans résultat donnent un resultat 
*)
let (+->) (a1 : ('res, 'term) ranalist) (a2 : 'term analist) :
  ('res, 'term) ranalist =
  fun l -> let r1,l1 = a1 l in (r1,a2 l1)
;;

type ('res ) parselist  =
  | 









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

let varOption : (char -> bexp option) = fun c -> 
  match c with 
  | 'a' -> Some(Ava 0)
  | 'b' -> Some(Ava 1)
  | 'c' -> Some(Ava 2)
  | 'd' -> Some(Ava 3)
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
let rVAR  : ((bexp, char) ranalist) = terminal_res varOption;;
let rA = rVAL +| rVAR;;

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
  fun (left : bexp) : (((winstr, char) ranalist)) ->
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
  rBLOCK (filter (list_of_string l) (list_of_string " \t\r")) ;;


let check : (winstr * (char list)) -> string = 
  fun (instr, l) ->
  match l with
  | [] -> winstrPrinter instr
  | _ -> "Erreur"  
;;
let test_WHILEb : (string -> unit) = fun s -> 
  print_string ("\n\n" ^ (check (rWHILEb s)) ^ "\n\n")
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

let rec evalBooleanExpression : (state -> bexp -> bool) = fun s exp ->
  match exp with
  | Bcst b            -> b
  | Ava i             -> (getValue s i)
  | And (left, right) -> (evalBooleanExpression s left) && (evalBooleanExpression s right)
  | Or (left, right)  -> (evalBooleanExpression s left) || (evalBooleanExpression s right)
  | Not (exp)         -> not (evalBooleanExpression s exp)
;;

let  rec update (s:state) (v:int) (n:bool): state =
  match v,s with
  | 0 , h :: d -> n :: d
  | 0 , []     -> n :: []
  | v1, h :: d -> h :: (update d (v1-1) n)
  | v1, []     -> false :: (update [] (v1-1) n)
;;


let evalAssign : (state -> bexp -> bexp -> state) = fun s left right ->
  match left with
  | Ava i -> update s i (evalBooleanExpression s right)
  | _ -> s
;;

type winstr =
  | Skip 
  | Assign of bexp * bexp
  | Seq of winstr * winstr
  | If of bexp * winstr * winstr
  | While of bexp * winstr
;;


let rec evalProgram : (state -> winstr -> state) = fun s instr ->
  match instr with 
  | Skip -> s
  | Assign (left, right) -> evalAssign s left right
  | Seq (left, right) -> let s = (evalProgram s left) in (evalProgram s right)
  | If (cond, if_then, if_else) -> 
      if (evalBooleanExpression s cond) 
        then (evalProgram e)
  | While (cond, while_do , while_done ) -> 
      if (evalBooleanExpression s ) then (evalProgram while_do)

  