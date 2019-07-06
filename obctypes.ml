(* obc *)
(* obctypes.ml *)
(* Developer: Branitskiy Alexander <schurshik@yahoo.com> *)

type qfloat = { isdefined: bool; rational: Q.t; scale: int; } (* isdefined, rational, scale *)

type assign_op =
  | OpAssign
  | PlusAssign
  | MinusAssign
  | MulAssign
  | DivAssign
  | ModAssign
  | PowAssign

type incr_decr =
  | Incr
  | Decr

type bin_op =
  | Plus
  | Minus
  | Mul
  | Div
  | Mod
  | Pow

type log_op =
  | Or
  | And

type rel_op =
  | Eq
  | Ne
  | Le
  | Ge
  | Lt
  | Gt

type square_braces_with_expr =
  | SquareBracesWithExpr of expression list
and
named_expression =
  | Value of string
  | ValueAtIndex of (string * expression list)
  | Scale
  | Ibase
  | Obase
and
expression =
  | NamedExpr of named_expression
  | Number of qfloat
  | Undef
  | Call of (string * opt_argument_list)
  | LogApply of (log_op * expression * expression)
  | InvertBool of expression
  | Apply of (bin_op * expression * expression)
  | Compare of (rel_op * expression * expression)
  | InvertSign of expression
  | PreAssign of (incr_decr * named_expression)
  | PostAssign of (incr_decr * named_expression)
  | Assign of (assign_op * named_expression * expression)
  | Ternary of (expression * expression * expression)
  | Length of expression
  | Sqrt of expression
  | ScaleWithArg of expression
  | Truncate of expression
and
argument_value =
  | ArgExpr of expression
  | ArgArr of (string * int)
and
opt_argument_list =
  | OptArguments of argument_value list

type return_expression =
  | Empty
  | RetExpr of expression

type argument_list =
  | Arguments of argument_value list

type letter_name =
  | Var of string
  | Arr of (string * int)

type define_list =
  | Define of letter_name list

type square_braces =
  | SquareBraces of int

type opt_auto_define_list =
  | AutoDefine of letter_name list

type opt_parameter_list =
  | OptParameters of letter_name list

type statement =
  | Expr of expression
  | String of string
  | Break
  | Continue
  | Quit
  | Exit of return_expression
  | Return of return_expression
  | For of (expression * expression * expression * statement)
  | If of (expression * statement)
  | IfElse of (expression * statement * statement)
  | While of (expression * statement)
  | StatementList of statement list

type statement_list =
  | Statements of statement list

type func =
  | Func of (string * opt_parameter_list * opt_auto_define_list  * statement_list)

type semicolon_list =
  | Semicolons of statement list

type input_item =
  | InputItem of statement list
  | DefFunc of (string * opt_parameter_list * opt_auto_define_list  * statement_list)

type program =
  | Program of input_item list
