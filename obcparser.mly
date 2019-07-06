/* obc */
/* obcparser.mly */
/* Developer: Branitskiy Alexander <schurshik@yahoo.com> */

%{
open Obctypes
%}

%token EOF

%token NEWLINE SEMICOLON COMMA

%token <string> STRING

%token <string> LETTER

%token <Obctypes.qfloat> NUMBER

%token OP_ASSIGN PLUS_ASSIGN MINUS_ASSIGN MUL_ASSIGN DIV_ASSIGN MOD_ASSIGN POW_ASSIGN

%token OR AND NOT

%token EQ NE LE GE LT GT

%token INCR DECR

%token DEF

%token BREAK

%token CONTINUE

%token QUIT

%token EXIT

%token LENGTH

%token QUESTION

%token COLON

%token RETURN

%token FOR IF ELSE WHILE 

%token SQRT

%token UNDEF

%token SCALE

%token TRUNCATE

%token IBASE

%token OBASE

%token AUTO

%token LEFT_CIRCLE_BRACE RIGHT_CIRCLE_BRACE

%token LEFT_FIGURE_BRACE RIGHT_FIGURE_BRACE

%token LEFT_SQUARE_BRACE RIGHT_SQUARE_BRACE

%token PLUS MINUS

%token MUL DIV MOD

%token POW

/* precedence levels */
%right OP_ASSIGN PLUS_ASSIGN MINUS_ASSIGN MUL_ASSIGN DIV_ASSIGN MOD_ASSIGN POW_ASSIGN
%nonassoc QUESTION
%left OR
%left AND
%nonassoc NOT
%left EQ NE LE GE LT GT
/* %right OP_ASSIGN PLUS_ASSIGN MINUS_ASSIGN MUL_ASSIGN DIV_ASSIGN MOD_ASSIGN POW_ASSIGN */
%left PLUS MINUS
%left MUL DIV MOD
%nonassoc IF
%nonassoc ELSE
%nonassoc UMINUS
%right POW
/* %nonassoc INCR DECR */

/* %start program

%type <Obctypes.program> program */

%start <Obctypes.program> program

%%

program: /* right recursion :( */
| EOF { Program [] }
| i = input_item p = program { match p with | Program v -> Program (i :: v) }

input_item:
| l = semicolon_list NEWLINE { match l with | Semicolons v -> InputItem v }
| f = func { match f with | Func v -> DefFunc v }

semicolon_list:
| /* empty */ { Semicolons [] }
| s = statement { Semicolons [s] }
| l = semicolon_list SEMICOLON s = statement { match l with | Semicolons v -> Semicolons (v @ [s]) }
| l = semicolon_list SEMICOLON { l }

func:
| DEF l = LETTER LEFT_CIRCLE_BRACE p = opt_parameter_list RIGHT_CIRCLE_BRACE opt_newline LEFT_FIGURE_BRACE NEWLINE d = opt_auto_define_list s = statement_list RIGHT_FIGURE_BRACE { Func (l, p, d, s) }

statement_list:
| /* empty */ { Statements [] }
| s = statement { Statements [s] }
| l = statement_list NEWLINE { l }
| l = statement_list NEWLINE s = statement { match l with | Statements v -> Statements (v @ [s]) }
| l = statement_list SEMICOLON { l }
| l = statement_list SEMICOLON s = statement { match l with | Statements v -> Statements (v @ [s]) }

opt_newline:
| /* empty */ { }
| opt_newline NEWLINE { }

statement:
| e = expression { Expr e }
| s = STRING { String s }
| BREAK { Break }
| CONTINUE { Continue }
| QUIT { Quit }
| EXIT e = return_expression { Exit e }
| RETURN e = return_expression { Return e }
| FOR LEFT_CIRCLE_BRACE e1 = expression SEMICOLON e2 = expression SEMICOLON e3 = expression RIGHT_CIRCLE_BRACE opt_newline s = statement { For (e1, e2, e3, s) }
| IF LEFT_CIRCLE_BRACE e = expression RIGHT_CIRCLE_BRACE opt_newline s = statement %prec IF { If (e, s) }
| IF LEFT_CIRCLE_BRACE e = expression RIGHT_CIRCLE_BRACE opt_newline s1 = statement ELSE opt_newline s2 = statement { IfElse (e, s1, s2) }
| WHILE LEFT_CIRCLE_BRACE e = expression RIGHT_CIRCLE_BRACE opt_newline s = statement { While (e, s) }
| LEFT_FIGURE_BRACE s = statement_list RIGHT_FIGURE_BRACE { match s with | Statements v -> StatementList v }

opt_parameter_list:
| /* empty */ { OptParameters [] }
| d = define_list { match d with Define d -> OptParameters d }

opt_auto_define_list:
| /* empty */ { AutoDefine [] }
| AUTO d = define_list NEWLINE { match d with | Define v -> AutoDefine v }
| AUTO d = define_list SEMICOLON { match d with | Define v -> AutoDefine v }

square_braces:
| LEFT_SQUARE_BRACE RIGHT_SQUARE_BRACE { SquareBraces 1 }
| s = square_braces LEFT_SQUARE_BRACE RIGHT_SQUARE_BRACE { match s with | SquareBraces n -> SquareBraces (n + 1) }

define_list:
| l = LETTER { Define [Var l] }
| l = LETTER s = square_braces { match s with | SquareBraces n -> Define [Arr (l, n)] }
| d = define_list COMMA l = LETTER { match d with | Define v -> Define (v @ [Var l]) }
| d = define_list COMMA l = LETTER s = square_braces { match d with | Define v -> match s with | SquareBraces n -> Define (v @ [Arr (l, n)]) }

argument_list:
| e = expression { Arguments [ArgExpr e] }
| l = LETTER s = square_braces { match s with | SquareBraces n -> Arguments [ArgArr (l, n)] }
| a = argument_list COMMA e = expression { match a with | Arguments v -> Arguments (v @ [ArgExpr e]) }
| a = argument_list COMMA l = LETTER s = square_braces { match a with | Arguments v -> match s with | SquareBraces n -> Arguments (v @ [ArgArr (l, n)]) }

return_expression:
| /* empty */ { Empty }
| e = expression { RetExpr e }

opt_argument_list:
| /* empty */ { OptArguments [] }
| a = argument_list { match a with Arguments v -> OptArguments v }

expression:
| v = named_expression { NamedExpr v }
| n = NUMBER { Number n }
| UNDEF { Undef }
| LEFT_CIRCLE_BRACE e = expression RIGHT_CIRCLE_BRACE { e }
| f = LETTER LEFT_CIRCLE_BRACE a = opt_argument_list RIGHT_CIRCLE_BRACE { Call (f, a) }
| e1 = expression o = log_op e2 = expression { LogApply (o, e1, e2) }
| NOT e = expression { InvertBool e }
| e1 = expression o = bin_op e2 = expression { Apply (o, e1, e2) }
| e1 = expression o = rel_op e2 = expression { Compare (o, e1, e2) }
| MINUS e = expression %prec UMINUS { InvertSign e }
| o = incr_decr v = named_expression { PreAssign (o, v) }
| v = named_expression o = incr_decr { PostAssign (o, v) }
| v = named_expression o = assign_op e = expression { Assign (o, v, e) }
| e1 = expression QUESTION e2 = expression COLON e3 = expression %prec QUESTION { Ternary (e1, e2, e3) }
| LENGTH LEFT_CIRCLE_BRACE e = expression RIGHT_CIRCLE_BRACE { Length e }
| SQRT LEFT_CIRCLE_BRACE e = expression RIGHT_CIRCLE_BRACE { Sqrt e }
| SCALE LEFT_CIRCLE_BRACE e = expression RIGHT_CIRCLE_BRACE { ScaleWithArg e }
| TRUNCATE LEFT_CIRCLE_BRACE e = expression RIGHT_CIRCLE_BRACE { Truncate e }

named_expression:
| l = LETTER { Value l }
| l = LETTER s = square_braces_with_expr { match s with | SquareBracesWithExpr exprs -> ValueAtIndex (l, exprs) }
| SCALE { Scale }
| IBASE { Ibase }
| OBASE { Obase }

square_braces_with_expr:
| LEFT_SQUARE_BRACE e = expression RIGHT_SQUARE_BRACE { SquareBracesWithExpr [e] }
| s = square_braces_with_expr LEFT_SQUARE_BRACE e = expression RIGHT_SQUARE_BRACE { match s with | SquareBracesWithExpr l -> SquareBracesWithExpr (l @ [e]) }

%inline rel_op:
| EQ { Eq }
| NE { Ne }
| LE { Le }
| GE { Ge }
| LT { Lt }
| GT { Gt }

%inline log_op:
| OR { Or }
| AND { And }

%inline bin_op:
| PLUS { Plus }
| MINUS { Minus }
| MUL { Mul }
| DIV { Div }
| MOD { Mod }
| POW { Pow }

%inline incr_decr:
| INCR { Incr }
| DECR { Decr }

%inline assign_op:
| OP_ASSIGN { OpAssign }
| PLUS_ASSIGN { PlusAssign }
| MINUS_ASSIGN { MinusAssign }
| MUL_ASSIGN { MulAssign }
| DIV_ASSIGN { DivAssign }
| MOD_ASSIGN { ModAssign }
| POW_ASSIGN { PowAssign }
