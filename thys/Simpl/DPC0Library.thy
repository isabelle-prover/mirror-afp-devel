(*  ID:          $Id: DPC0Library.thy,v 1.3 2008-03-07 15:23:43 lsf37 Exp $
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

header {* DPC0 standard library *}

theory DPC0Library imports DPC0Expressions Vcg begin

text {* This theory constitutes a standard library for DPC0 programs.  At
 first, it includes (indirectly) the C0 library and (directly) its extensions
 for DPC0 specific expressions.  Secondly, the Vcg of the verification
 environment is included and its syntax extended by the DPC0 specific
 statement constructs for contextualization.
*}


(* =================================================== *)
section {* Auxiliary functions for the concrete syntax *}
(* =================================================== *)


consts pfilter:: "bool list \<Rightarrow> 'a list \<Rightarrow> 'a list"
primrec
"pfilter c [] = []"
"pfilter c (v#vs) = (if hd c then v#pfilter (tl c) vs else pfilter (tl c) vs)" 


consts pmask:: "nat \<Rightarrow> bool list \<Rightarrow> nat list"
primrec
"pmask i  [] = []"
"pmask i (b#bs) = (if b then i#(pmask (Suc i) bs) else pmask (Suc i) bs)"


(* ============================================= *)
section {* Concrete syntax for Contextualization *}
(* ============================================= *)

syntax
  "_In":: "[ident,'a,'a] \<Rightarrow> ('s,'p,'f) com"
                 ("(2 IN \<acute>_:/ _ :== _)" [1000,30,30] 21)
  "_Where":: "['a,ident,('s,'p,'f) com] \<Rightarrow> ('s,'p,'f) com" 
                 ("(0 WHERE (_)/ FOR \<acute>_ DO/ _ EREHW)" [0,0,0] 71)
  "_WhereElse":: "['a,ident,('s,'p,'f) com,('s,'p,'f) com] \<Rightarrow> ('s,'p,'f) com"
                 ("(0 WHERE (_)/ FOR \<acute>_ DO/ _ ELSE _ EREHW)" [0,0,0,0] 71)


translations
  "_In c (x!!i) y" => "x!!(pfilter \<acute>c i) :== pfilter \<acute>c y"
  "_In c x y" => "x!!(pmask 0 \<acute>c) :== pfilter \<acute>c y"
  "_Where m c s" => "_Loc (_locinit c (p_and \<acute>c m)) s"
  "_WhereElse m c s1 s2" => "(_Loc (_locinit c (p_and \<acute>c m)) s1);;
                             (_Loc (_locinit c (p_and \<acute>c (p_not m))) s2)"

print_translation {*
let
fun in_tr' [Const ("list_multsel",_)$x$
               (Const ("pfilter",_)$(Const ("_antiquoteCur",_)$c)$i),
            Const ("pfilter",_)$(Const ("_antiquoteCur",_)$c')$y] =
     if c=c'
     then Syntax.const "_In"$c$(Syntax.const "list_multsel"$x$i)$y
     else raise Match 
  | in_tr' [Const ("list_multsel",_)$x$
               (Const ("pmask",_)$z$(Const ("_antiquoteCur",_)$c)),
            Const ("pfilter",_)$(Const ("_antiquoteCur",_)$c')$y] =
     if c=c'
     then Syntax.const "_In"$c$x$y
     else raise Match 

fun where_tr' [Const ("_locinit",_)$Const (c,_)$
                  (Const ("p_and",_)$(Const ("_antiquoteCur",_)$Const (c',_))$m),
               s] =
     if c=c' then Syntax.const "_Where"$m$Syntax.const c$s else raise Match
  | where_tr' ts = raise Match
in [("_Assign",in_tr'),
    ("_Loc",where_tr')] end

*}

print_ast_translation {*
let
fun where_else_tr' [Appl [Constant "_Where", m, c, s1],
                    Appl [Constant "_Where", Appl [Constant "p_not",m'],c',s2]] = 
     if c=c' andalso m=m' 
     then Appl [Constant "_WhereElse",m,c,s1,s2]
     else raise Match

in [("_seq",where_else_tr')] end
*}


end
