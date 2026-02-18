type ident = Ident of string
type date = { day : int; month : int; year : int }

type exp =
	| Var of ident
	| Bool of bool
	| Int of int
	| Plus of exp * exp
	| Tuple of exp * exp
	| Date of date

let explode str = List.init (String.length str) (String.get str)
let implode chrs = String.init (List.length chrs) (List.nth chrs)

(* Razčlenjevalnik:
	 Za nek seznam znakov ali
		 - uspešno (razčleni) vrne par razčlenjene vrednosti in preostanka
		 - neuspešno vrne None - to pomeni, da seznam znakov ni ustrezal pričakovanemu vzorcu
*)

type 'value result = ('value * char list) option
type 'value parser = char list -> 'value result

(* Nekaj najenostavnejših *)

(* Vedno neuspešno *)
let fail _ = None

(* Vedno uspešno	- Ne porabi znakov *)
let return v chrs = Some (v, chrs)

(* Razčleni en znak *)
let single_character = function [] -> None | chr :: chrs -> Some (chr, chrs)

(*
	 Kombiniramo dva razčlenjevalnika parser1 in parser2 tako,
	 da najprej poskusimo parser1, če ta ne uspe, pa poskusimo parser2.
*)
let ( || ) (parser1 : 'a parser) (parser2 : 'a parser) (chrs : char list) :
    'a result =
	match parser1 chrs with
	| None -> parser2 chrs
	| Some (v, chrs') -> Some (v, chrs')

(*
	Najprej poskusimo parser1, če ta uspe, pa uporabimo dobljeno vrednost v parser2.	
	Temu se baje rece bind.
*)
let ( >>= ) (parser1 : 'a parser) (parser2 : 'a -> 'b parser) (chrs : char list)
    : 'b result =
	match parser1 chrs with
	| None -> None
	| Some (v, chrs') -> parser2 v chrs'



(* Porabimo prvega in zavržemo, ter takoj nadaljujemo z drugim *)
let ( >> ) (parser1 : 'a parser) (parser2 : 'b parser) : 'b parser =
	parser1 >>= fun _ -> parser2

(*
	Ustvari nov razčlenjevalnik, ki razčleni če podan pogoj velja za dobljeno vrednost.
*)
(*
let satisfy (cond : 'a -> bool) (parser : 'a parser) chrs : 'a parser =
	match parser chrs with
	| None -> None
	| Some(v, chrs') -> if cond v then return v chrs' else fail
		*)
let satisfy (cond : 'a -> bool) (parser : 'a parser) : 'a parser =
	parser >>= fun v ->
		match cond v with
		| true -> return v
		| false -> fail
		

(* Razčleni eno števko *)

let digit : char parser =
	satisfy (fun d -> match d with | '0' .. '9' -> true | _ -> false) single_character
let alpha : char parser =
	satisfy (fun c -> match c with | 'a' .. 'z' -> true | _ -> false) single_character
		(*
let digit : char parser = 
	single_character >>= fun d ->
		match d with
		| '0' .. '9' -> return d
		| _ -> fail
let alpha : char parser = 
	single_character >>= fun d ->
		match d with
		| 'a' .. 'z' -> return d
		| _ -> fail*)

let space : char parser =
	let is_space = String.contains " \n\t\r" in
	single_character |> satisfy is_space

let exactly (chr : char) : char parser = single_character |> satisfy (( = ) chr)
let rec one_of (parsers : 'a parser list) : 'a parser =
  match parsers with
  | [] -> fail
  | fst :: tail -> fst || (one_of tail)

(* Razčleni besedo in jo ignorira *)
let word (str : string) : unit parser =
	let chrs = explode str in
	List.fold_right (fun chr parser -> exactly chr >> parser) chrs (return ())

(* Razčleni `parser*` in `parser+` *)
let rec many (parser : 'a parser) : 'a list parser = many1 parser || return []

and many1 (parser : 'a parser) : 'a list parser =
	parser >>= fun v ->
	many parser >>= fun vs -> return (v :: vs)

(* Razčleni celo število *)
let integer : int parser =
	many1 digit >>= fun v -> implode v |> int_of_string |> return
	(*many1 digit >>= (fun v -> return (int_of_string (implode v)))*)

let spaces : unit parser = many space >> return ()
let spaces1 : unit parser = many1 space >> return ()

(*
 razčleni izraze oblike `(izraz)` - kjer so lahko okoli oklepajev presledki
 word zato, ker je to kasnej lazi popravlat (sicer exactly '('/')')
*)
let parens (parser : 'a parser) : 'a parser =
	word "(" >> spaces >> parser >>= fun r -> (spaces >> word ")") >> return r

(*
	Razčleni izraze oblike `izraz1 op izraz2` - kjer so lahko okoli operatorja presledki, in uporabi funkcijo `f` za združitev dobljenih vrednosti.
*)
let binop (parser1 : 'a parser) (op : string) (parser2 : 'b parser)
		(f : 'a -> 'b -> 'c) : 'c parser =
	parser1 >>= fun l -> spaces >> word op >> spaces >> parser2 >>= fun r -> f l r |> return

let ident =
	alpha >>= fun chr ->
	many (alpha || digit || exactly '\'') >>= fun chrs ->
	return (Ident (implode (chr :: chrs)))

(* I have no idea what the month and date formats should look like *)
let month_parser : int parser = fail
let date_parser : date parser = fail

let rec exp1 chrs =
	one_of [ binop exp0 "+" exp1 (fun e1 e2 -> Plus (e1, e2)); exp0 ] chrs

and exp0 chrs =
	one_of
		[
			(date_parser >>= fun d -> return (Date d));
			(integer >>= fun n -> return (Int n));
			word "TRUE" >> return (Bool true);
			word "FALSE" >> return (Bool false);
			(ident >>= fun x -> return (Var x));
			parens exp1;
		]
		chrs

let parse str =
	match str |> String.trim |> explode |> exp1 with
	| Some (v, []) -> v
	| Some (_, _ :: _) | None -> failwith "Parsing error"

let a = parse "1+2+(3+4)"
