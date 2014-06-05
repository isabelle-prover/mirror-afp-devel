open Ltl_Dt
open Propc
%%
%name Ltl

%term NOT    | OR     | AND 
    | IMPL   | IFF
    | TRUE   | FALSE
    | NEXT   | FINAL  | GLOBAL
    | UNTIL  | RELEASE
    | LPAREN | RPAREN
    | LBRACK | RBRACK
    | EQ | NEQ | GR | GEQ | LE | LEQ
    | IDENT of string
    | IDENT_EXPR of int
    | EOF | BAD_CHAR

%left IFF
%left IMPL
%left AND OR
%left UNTIL RELEASE

%nonassoc NEXT FINAL GLOBAL
%nonassoc NOT

%nonterm input of propc ltlc 
       | formula of propc ltlc
       | expr of propc ltlc
       | ident of ident
       | bop of binOp

%pos int

%eop EOF
%noshift EOF

(* %verbose *)
%start input
%pure

%%

input: formula (formula)

formula: expr			 (expr)
       | TRUE			 (LTLcTrue)
       | FALSE			 (LTLcFalse)
       | NOT formula		 (LTLcNeg formula)
       | NEXT formula		 (LTLcNext formula)
       | FINAL formula		 (LTLcFinal formula)
       | GLOBAL formula		 (LTLcGlobal formula)
       | formula OR formula	 (LTLcOr (formula1, formula2))
       | formula AND formula 	 (LTLcAnd (formula1, formula2))
       | formula IMPL formula (LTLcImplies (formula1, formula2))
       | formula IFF formula     (LTLcIff (formula1, formula2))
       | formula UNTIL formula	 (LTLcUntil (formula1, formula2))
       | formula RELEASE formula (LTLcRelease (formula1, formula2))
       | LPAREN formula RPAREN   (formula)

ident: IDENT LBRACK IDENT_EXPR RBRACK      (Ident (IDENT, SOME IDENT_EXPR))
     | IDENT                (Ident (IDENT, NONE))

expr: ident NEQ IDENT_EXPR (LTLcNeg (LTLcProp (BExpProp (Eq, ident, IDENT_EXPR))))
    | ident NEQ ident      (LTLcNeg (LTLcProp (BProp (Eq, ident1, ident2))))
    | ident bop IDENT_EXPR  (LTLcProp (BExpProp (bop, ident, IDENT_EXPR)))
    | ident bop ident       (LTLcProp (BProp (bop, ident1, ident2)))
    | ident                 (LTLcProp (CProp ident))

bop: EQ  (Eq)
  | LE  (Le)
  | LEQ (LEq)
  | GR  (Gr)
  | GEQ (GEq)

(* 
 * vim: ft=yacc 
 *)
