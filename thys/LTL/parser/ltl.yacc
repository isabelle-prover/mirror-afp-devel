open Ltl_Dt
%%
%name Ltl

%term NOT    | OR     | AND 
    | IMPL   | IFF
    | TRUE   | FALSE
    | NEXT   | FINAL  | GLOBAL
    | UNTIL  | RELEASE
    | LPAREN | RPAREN
    | IDENT of string
    | EOF | BAD_CHAR

%left IFF
%left IMPL
%left AND OR
%left UNTIL RELEASE

%nonassoc NEXT FINAL GLOBAL
%nonassoc NOT

%nonterm input of string ltlc 
       | formula of string ltlc

%pos int

%eop EOF
%noshift EOF

(* %verbose *)
%start input
%pure

%%

input: formula (formula)

formula: IDENT			 (LTLcProp IDENT)
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

(* 
 * vim: ft=yacc 
 *)
