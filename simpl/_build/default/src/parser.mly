%{
open Ast
%}

%token <int> INT
%token <string> VAR
%token <float> FLOAT
%token TRUE
%token FALSE
%token LEQ
%token LEQF
%token TIMES  
%token PLUS
%token LPAREN
%token RPAREN
%token LET
%token EQUALS
%token IN
%token IF
%token THEN
%token ELSE
%token EOF

%token POWER
%token TIMESF  
%token PLUSF
%token POWERF

%nonassoc IN
%nonassoc ELSE
%left LEQ
%left LEQF
%left PLUS
%left TIMES  
%left POWER
%left PLUSF
%left TIMESF
%left POWERF

%start <Ast.expr> prog

%%

prog:
	| e = expr; EOF { e }
	;
	
expr:
	| i = INT { Int i }
	| y = FLOAT { Float y}
	| x = VAR { Var x }
	| TRUE { Bool true }
	| FALSE { Bool false }
	| e1 = expr; LEQ; e2 = expr { Binop (Leq, e1, e2) }
	| e1 = expr; LEQF; e2 = expr { Binop (Leq, e1, e2) }
	| e1 = expr; TIMES; e2 = expr { Binop (Mult, e1, e2) } 
	| e1 = expr; PLUS; e2 = expr { Binop (Add, e1, e2) }
	// Things I changed
	| e1 = expr; POWER; e2 = expr { Binop (Power, e1, e2) }	
	| e1 = expr; PLUSF; e2 = expr { Binop (Addf, e1, e2) }	
	| e1 = expr; TIMESF; e2 = expr { Binop (Multf, e1, e2) }	
	| e1 = expr; POWERF; e2 = expr { Binop (Powerf, e1, e2) }	

	| LET; x = VAR; EQUALS; e1 = expr; IN; e2 = expr { Let (x, e1, e2) }
	| IF; e1 = expr; THEN; e2 = expr; ELSE; e3 = expr { If (e1, e2, e3) }
	| LPAREN; e=expr; RPAREN {e} 
	;
	
