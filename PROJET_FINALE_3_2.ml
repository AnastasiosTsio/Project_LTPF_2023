type bexp = 
  | Bcst of bool
  | Ava of string
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
let terminal_cond_res (p : 'term -> bool) : ('res ,'term) ranalist= function
  | x :: l when p x -> (x,l)
  | _ -> raise Echec
;;

(* Corresponding to previous language *)
type token =
  | Boolean of bool (* 1|0*)
  | Variable of string (* x *)
  | OpenBrace (* { *)
  | CloseBrace (* }*)
  | Semicolon (* ; *)
  | Assignement (* := *)
  | While (* while *)
  | If (* if *)
  | Then (* then *)
  | Else (* else *)
  | Not (* ! *)
  | And (* && *)
  | Or (* || *)
  | ParenthesisOpen (* ( *)
  | ParenthesisClose (* ) *)
;;

(* Lexing *)
let is_alpha_numeric c =
  (Char.code c >= Char.code 'a' && Char.code c <= Char.code 'z') ||
  (Char.code c >= Char.code 'A' && Char.code c <= Char.code 'Z') ||
  (Char.code c >= Char.code '0' && Char.code c <= Char.code '9')


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

let exprLex : ((token, char) ranalist) = 
  fun l -> l 
           |>
           (terminal_string "true" -+> epsilon_res (Boolean true))
           +|
           (terminal_string "false" -+> epsilon_res (Boolean false))
           +|
           (terminal_string "{" -+> epsilon_res (OpenBrace))
           +|
           (terminal_string "}" -+> epsilon_res (CloseBrace))
           +|
           (terminal_string ";" -+> epsilon_res (Semicolon))
           +|
           (terminal_string ":=" -+> epsilon_res (Assignement))
           +|
           (terminal_string "while" -+> epsilon_res (While))
           +|
           (terminal_string "if" -+> epsilon_res (If))
           +|
           (terminal_string "then" -+> epsilon_res (Then))
           +|
           (terminal_string "else" -+> epsilon_res (Else))
           +|
           (terminal_string "!" -+> epsilon_res (Not))
           +|
           (terminal_string "&&" -+> epsilon_res (And))
           +|
           (terminal_string "||" -+> epsilon_res (Or))
           +|
           (terminal_string "(" -+> epsilon_res (ParenthesisOpen))
           +|
           (terminal_string ")" -+> epsilon_res (ParenthesisClose))
;;


let lexer : (token list, char) ranalist = star_list exprLex ;;

(* Test *)

let test_lexer = lexer (list_of_string "if (abcde) then {x := true;} else {x := false;}");;

(* Parsing *)


