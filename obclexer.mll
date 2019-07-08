(* obc *)
(* obclexer.mll *)
(* Developer: Branitskiy Alexander <schurshik@yahoo.com> *)

{
open Lexing
open Obcparser
open Obctypes
exception SyntaxError of string

let raise_lex_error lexbuf =
  raise (let p = Lexing.lexeme_start_p lexbuf in
         SyntaxError (Printf.sprintf "Incorrect symbol %s at offset %d in the line %d\n" (Lexing.lexeme lexbuf) (p.pos_cnum - p.pos_bol) p.pos_lnum));;

let goto_next_line lexbuf =
  let p = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { p with pos_bol = lexbuf.lex_curr_pos;
             pos_lnum = p.pos_lnum + 1 }

let make_qval ?(def=true) str scl =
  { isdefined = def; rational = Q.of_string str; scale = scl; }

let make_undef_qval () =
  make_qval ~def:false "0" 0

let isdefined_of_qval qval = qval.isdefined

let rational_of_qval qval = qval.rational

let scale_of_qval qval = qval.scale

let ibase_ref = ref 10

let qval_of_string str =
  let reg_exp = Str.regexp "^\\([0-9A-Z]+\\)\\(\\(\\.\\([0-9A-Z]*\\)\\)?\\)\\(\\([e]\\([-+]?\\)\\([0-9A-Z]+\\)\\)?\\)$" in
  let rec decode_str_to_z10 ?(first_call=true) s from_base =
    if s = "" then
      (if first_call then raise (SyntaxError "string is empty") else Z.zero)
    else
      let first_addition = Z.mul (Z.of_int from_base) (decode_str_to_z10 ~first_call:false (String.sub s 0 ((String.length s) - 1)) from_base) in
      let last_symbol = String.get s ((String.length s) - 1) in
      let is_big_alpha c = (Char.code c) >= (Char.code 'A') && (Char.code c) <= (Char.code 'Z') in
      let second_addition = Z.of_int ((Char.code last_symbol) - (if is_big_alpha last_symbol then (Char.code 'A') - 10 else Char.code '0')) in
      Z.add first_addition second_addition in
  let int_part = Z.to_string (decode_str_to_z10 (Str.replace_first reg_exp "\\1" str) !ibase_ref) in
  let frac_part = try Z.to_string (decode_str_to_z10 (Str.replace_first reg_exp "\\4" str) !ibase_ref) with
                  | Failure _ -> "" in
  let sign_exp_part = try Z.to_string (decode_str_to_z10 (Str.replace_first reg_exp "\\7" str) !ibase_ref) with
                      | Failure _ -> "+" in
  let exp_part = try Z.to_string (decode_str_to_z10 (Str.replace_first reg_exp "\\8" str) !ibase_ref) with
                 | Failure _ -> "0" in
  let concat_list l = String.concat "" l in
  let fill_zero s = String.make s '0' in
  let fill_zero_if b n = if b then fill_zero n else "" in  
  let numerator = concat_list [int_part; frac_part; fill_zero_if (sign_exp_part = "+") (int_of_string exp_part)] in
  let denominator = concat_list ["1"; fill_zero (String.length frac_part); fill_zero_if (sign_exp_part = "-") (int_of_string exp_part)] in
  let ratio_number = Printf.sprintf "%s/%s" numerator denominator in
  let ratio_number_scale = max 0 ((String.length frac_part) + (if sign_exp_part = "+" then -1 else 1) * (int_of_string exp_part)) in
  make_qval ratio_number ratio_number_scale
}

let digit = ['0'-'9' 'A'-'Z']
let int_number = digit+
let frac = '.' digit*
let exp = 'e' ['-' '+']? digit+
let float_number = digit+ frac? exp?
let number = int_number | float_number
let white = [' ' '\t']
(* let alpha = ['a'-'z' 'A'-'Z'] *)
let word = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*
let newline = '\n'
let comment = '#' [^ '\n']*
let scale_token = "scale"
let truncate_token = "truncate"
let print_token = "print"
let ibase_token = "ibase"
let obase_token = "obase"
(* let newline = '\n' | "\r\n" *)

rule read_tokens = parse
| white { read_tokens lexbuf }
| '\\' newline { goto_next_line lexbuf; read_tokens lexbuf }
| newline { goto_next_line lexbuf; NEWLINE }
| comment { read_tokens lexbuf }
| ';' { SEMICOLON }
| ',' { COMMA }
| '"' { read_string (Buffer.create 0) lexbuf } (* size is automatically increased *)
| '=' { OP_ASSIGN }
| "+=" { PLUS_ASSIGN }
| "-=" { MINUS_ASSIGN }
| "*=" { MUL_ASSIGN }
| "/=" { DIV_ASSIGN }
| "%=" { MOD_ASSIGN }
| "^=" { POW_ASSIGN }
| "==" { EQ }
| "!=" { NE }
| "<=" { LE }
| ">=" { GE }
| '<' { LT }
| '>' { GT }
| "||" { OR }
| "&&" { AND }
| '!' { NOT }
| "++" { INCR }
| "--" { DECR }
| '?' { QUESTION }
| ':' { COLON }
| "define" { DEF }
| "break" { BREAK }
| "continue" { CONTINUE }
| "quit" { QUIT }
| "exit" { EXIT }
| "length" { LENGTH }
| "return" { RETURN }
| "for" { FOR }
| "if" { IF }
| "else" { ELSE }
| "while" { WHILE }
| "sqrt" { SQRT }
| scale_token { SCALE }
| truncate_token { TRUNCATE }
| print_token { PRINT }
| ibase_token { IBASE }
| obase_token { OBASE }
| "auto" { AUTO }
| "undef" { UNDEF }
| word { LETTER (Lexing.lexeme lexbuf) }
| number { NUMBER (qval_of_string (Lexing.lexeme lexbuf)) }
| '(' { LEFT_CIRCLE_BRACE }
| ')' { RIGHT_CIRCLE_BRACE }
| '{' { LEFT_FIGURE_BRACE }
| '}' { RIGHT_FIGURE_BRACE }
| '[' { LEFT_SQUARE_BRACE }
| ']' { RIGHT_SQUARE_BRACE }
| '+' { PLUS }
| '-' { MINUS }
| '*' { MUL }
| '/' { DIV }
| '%' { MOD }
| '^' { POW }
| eof { EOF }
| _ { raise_lex_error lexbuf }

and

read_string buf = parse
| '\\' '"' { Buffer.add_char buf '"'; read_string buf lexbuf }
| '"' { STRING (Buffer.contents buf) }
| '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
| '\\' 'b' { Buffer.add_char buf '\b'; read_string buf lexbuf }
| '\\' 'f' { Buffer.add_char buf '\012'; read_string buf lexbuf }
| '\\' 'n' { Buffer.add_char buf '\n'; read_string buf lexbuf }
| '\\' 'r' { Buffer.add_char buf '\r'; read_string buf lexbuf }
| '\\' 't' { Buffer.add_char buf '\t'; read_string buf lexbuf }
| [^ '\\' '"']+ { Buffer.add_string buf (Lexing.lexeme lexbuf); read_string buf lexbuf }
| _ { raise_lex_error lexbuf }
