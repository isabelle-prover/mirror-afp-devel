(*  Title:      Vcg.thy
    Author:     Norbert Schirmer, TU Muenchen

Copyright (C) 2004-2008 Norbert Schirmer 
Some rights reserved, TU Muenchen

This library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of the
License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA
*)

header {* Facilitating the Hoare Logic *}
theory Vcg imports StateSpace "$ISABELLE_HOME/src/HOL/Statespace/StateSpaceLocale" Generalise
uses "hoare_package.ML" "hoare_syntax.ML" begin 


setup HoarePackage.setup
setup {* Context.theory_map 
          (HoarePackage.install_generate_guard HoareSyntax.mk_guard) *}

method_setup hoare = "HoarePackage.hoare"
  "raw verification condition generator for Hoare Logic"

method_setup hoare_raw = "HoarePackage.hoare_raw"
  "even more raw verification condition generator for Hoare Logic"

method_setup vcg = "HoarePackage.vcg" 
  "verification condition generator for Hoare Logic"

method_setup vcg_step = "HoarePackage.vcg_step" 
  "single verification condition generation step with light simplification"


method_setup hoare_rule = "HoarePackage.hoare_rule" 
  "apply single hoare rule and solve certain sideconditions"

consts NoBody::"('s,'p,'f) com"
finalconsts NoBody

text {* Variables of the programming language are represented as components 
of a record. To avoid cluttering up the namespace of Isabelle with lots of 
typical variable names, we append a unusual suffix at the end of each name by 
parsing
*}

constdefs list_multsel:: "'a list \<Rightarrow> nat list \<Rightarrow> 'a list" (infixl "!!" 100)
"xs !! ns \<equiv> map (nth xs) ns"

constdefs list_multupd:: "'a list \<Rightarrow> nat list \<Rightarrow> 'a list \<Rightarrow> 'a list"
"list_multupd xs ns ys \<equiv> foldl (\<lambda>xs (n,v). xs[n:=v]) xs (zip ns ys)"

nonterminals lmupdbinds lmupdbind

syntax
  -- {* multiple list update *}
  "_lmupdbind":: "['a, 'a] => lmupdbind"    ("(2_ [:=]/ _)")
  "" :: "lmupdbind => lmupdbinds"    ("_")
  "_lmupdbinds" :: "[lmupdbind, lmupdbinds] => lmupdbinds"    ("_,/ _")
  "_LMUpdate" :: "['a, lmupdbinds] => 'a"    ("_/[(_)]" [900,0] 900)

translations


  "_LMUpdate xs (_lmupdbinds b bs)"== "_LMUpdate (_LMUpdate xs b) bs"
  "xs[is[:=]ys]" == "list_multupd xs is ys"


subsection {* Some Fancy Syntax *}


(* priority guidline:
 * If command should be atomic for the guard it must have at least priority 21.
 *)

text {* reverse application *}
constdefs rapp:: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b" (infixr "|>" 60)
"rapp x f \<equiv> f x"


nonterminals newinit newinits locinit locinits switchcase switchcases
             grds grd bdy basics basic basicblock





syntax
  
  "_skip" :: "('s,'p,'f) com"                   ("SKIP")
  "_throw":: "('s,'p,'f) com"                   ("THROW")
  "_raise":: "'c \<Rightarrow> 'c \<Rightarrow> ('a,'b,'f) com"       ("(RAISE _ :==/ _)" [30, 30] 23)
  "_seq"::"('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com" ("_;;/ _" [20, 21] 20)
  "_guarantee"     :: "'s set \<Rightarrow> grd"       ("_\<surd>" [1000] 1000)
  "_guaranteeStrip":: "'s set \<Rightarrow> grd"       ("_#" [1000] 1000)
  "_grd"           :: "'s set \<Rightarrow> grd"       ("_" [1000] 1000)
  "_last_grd"      :: "grd \<Rightarrow> grds"         ("_" 1000)
  "_grds"          :: "[grd, grds] \<Rightarrow> grds" ("_,/ _" [999,1000] 1000)
  "_guards"        :: "grds \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com" 
                                            ("(_/\<longmapsto> _)" [60, 21] 23)                                                           
  "_quote"       :: "'b => ('a => 'b)"       (*("(.'(_').)" [0] 1000)*)
  "_antiquoteCur"  :: "('a => 'b) => 'b"       ("\<acute>_" [1000] 1000)
  "_antiquoteOld"  :: "('a => 'b) => 'a => 'b"       ("\<^bsup>_\<^esup>_" [1000,1000] 1000)
  "_Assert"      :: "'a => 'a set"           ("({|_|})" [0] 1000)
  "_AssertState" :: "idt \<Rightarrow> 'a \<Rightarrow> 'a set"    ("({|_. _|})" [1000,0] 1000)
  "_Assign"      :: "'b => 'b => ('a,'p,'f) com"    ("(_ :==/ _)" [30, 30] 23)
  "_Init"        :: "ident \<Rightarrow> 'c \<Rightarrow> 'b \<Rightarrow> ('a,'p,'f) com" 
                                             ("(\<acute>_ :==\<^bsub>_\<^esub>/ _)" [30,1000, 30] 23)
  "_GuardedAssign":: "'b => 'b => ('a,'p,'f) com"    ("(_ :==\<^sub>g/ _)" [30, 30] 23)
  "_newinit"      :: "[ident,'a] \<Rightarrow> newinit" ("(2\<acute>_ :==/ _)")
  ""             :: "newinit \<Rightarrow> newinits"    ("_")
  "_newinits"    :: "[newinit, newinits] \<Rightarrow> newinits" ("_,/ _")
  "_New"         :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f) com" 
                                            ("(_ :==/(2 NEW _/ [_]))" [30, 65, 0] 23)
  "_GuardedNew"  :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f) com" 
                                            ("(_ :==\<^sub>g/(2 NEW _/ [_]))" [30, 65, 0] 23)
  "_NNew"         :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f) com" 
                                            ("(_ :==/(2 NNEW _/ [_]))" [30, 65, 0] 23)
  "_GuardedNNew"  :: "['a, 'b, newinits] \<Rightarrow> ('a,'b,'f) com" 
                                            ("(_ :==\<^sub>g/(2 NNEW _/ [_]))" [30, 65, 0] 23)

  "_Cond"        :: "'a bexp => ('a,'p,'f) com => ('a,'p,'f) com => ('a,'p,'f) com"
        ("(0IF (_)/ (2THEN/ _)/ (2ELSE _)/ FI)" [0, 0, 0] 71)
  "_Cond_no_else":: "'a bexp => ('a,'p,'f) com => ('a,'p,'f) com"
        ("(0IF (_)/ (2THEN/ _)/ FI)" [0, 0] 71)
  "_GuardedCond" :: "'a bexp => ('a,'p,'f) com => ('a,'p,'f) com => ('a,'p,'f) com"
        ("(0IF\<^sub>g (_)/ (2THEN _)/ (2ELSE _)/ FI)" [0, 0, 0] 71)
  "_GuardedCond_no_else":: "'a bexp => ('a,'p,'f) com => ('a,'p,'f) com"
        ("(0IF\<^sub>g (_)/ (2THEN _)/ FI)" [0, 0] 71)
  "_While_inv_var"   :: "'a bexp => 'a assn  \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bdy 
                          \<Rightarrow> ('a,'p,'f) com"
        ("(0WHILE (_)/ INV (_)/ VAR (_) /_)"  [25, 0, 0, 81] 71)
  "_WhileFix_inv_var"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow> 
                            ('z \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> bdy 
                          \<Rightarrow> ('a,'p,'f) com"
        ("(0WHILE (_)/ FIX _./ INV (_)/ VAR (_) /_)"  [25, 0, 0, 0, 81] 71)
  "_WhileFix_inv"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow> bdy 
                          \<Rightarrow> ('a,'p,'f) com"
        ("(0WHILE (_)/ FIX _./ INV (_) /_)"  [25, 0, 0, 81] 71)
  "_GuardedWhileFix_inv_var"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow> 
                            ('z \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> bdy 
                          \<Rightarrow> ('a,'p,'f) com"
        ("(0WHILE\<^sub>g (_)/ FIX _./ INV (_)/ VAR (_) /_)"  [25, 0, 0, 0, 81] 71)
  "_GuardedWhileFix_inv_var_hook"   :: "'a bexp \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow> 
                            ('z \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> bdy 
                          \<Rightarrow> ('a,'p,'f) com"
  "_GuardedWhileFix_inv"   :: "'a bexp => pttrn \<Rightarrow> ('z \<Rightarrow> 'a assn)  \<Rightarrow> bdy 
                          \<Rightarrow> ('a,'p,'f) com"
        ("(0WHILE\<^sub>g (_)/ FIX _./ INV (_)/_)"  [25, 0, 0, 81] 71)

  "_GuardedWhile_inv_var":: 
       "'a bexp => 'a assn  \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> bdy \<Rightarrow> ('a,'p,'f) com"
        ("(0WHILE\<^sub>g (_)/ INV (_)/ VAR (_) /_)"  [25, 0, 0, 81] 71)
  "_While_inv"   :: "'a bexp => 'a assn => bdy => ('a,'p,'f) com"
        ("(0WHILE (_)/ INV (_) /_)"  [25, 0, 81] 71)
  "_GuardedWhile_inv"   :: "'a bexp => 'a assn => ('a,'p,'f) com => ('a,'p,'f) com"
        ("(0WHILE\<^sub>g (_)/ INV (_) /_)"  [25, 0, 81] 71)
  "_While"       :: "'a bexp => bdy => ('a,'p,'f) com"
        ("(0WHILE (_) /_)"  [25, 81] 71)
  "_GuardedWhile"       :: "'a bexp => bdy => ('a,'p,'f) com"
        ("(0WHILE\<^sub>g (_) /_)"  [25, 81] 71)
  "_While_guard"       :: "grds => 'a bexp => bdy => ('a,'p,'f) com"
        ("(0WHILE (_/\<longmapsto> (1_)) /_)"  [1000,25,81] 71)
  "_While_guard_inv":: "grds \<Rightarrow>'a bexp\<Rightarrow>'a assn\<Rightarrow>bdy \<Rightarrow> ('a,'p,'f) com"
        ("(0WHILE (_/\<longmapsto> (1_)) INV (_) /_)"  [1000,25,0,81] 71)
  "_While_guard_inv_var":: "grds \<Rightarrow>'a bexp\<Rightarrow>'a assn\<Rightarrow>('a\<times>'a) set
                             \<Rightarrow>bdy \<Rightarrow> ('a,'p,'f) com"
        ("(0WHILE (_/\<longmapsto> (1_)) INV (_)/ VAR (_) /_)"  [1000,25,0,0,81] 71)
  "_WhileFix_guard_inv_var":: "grds \<Rightarrow>'a bexp\<Rightarrow>pttrn\<Rightarrow>('z\<Rightarrow>'a assn)\<Rightarrow>('z\<Rightarrow>('a\<times>'a) set)
                             \<Rightarrow>bdy \<Rightarrow> ('a,'p,'f) com"
        ("(0WHILE (_/\<longmapsto> (1_)) FIX _./ INV (_)/ VAR (_) /_)"  [1000,25,0,0,0,81] 71)
  "_WhileFix_guard_inv":: "grds \<Rightarrow>'a bexp\<Rightarrow>pttrn\<Rightarrow>('z\<Rightarrow>'a assn)
                             \<Rightarrow>bdy \<Rightarrow> ('a,'p,'f) com"
        ("(0WHILE (_/\<longmapsto> (1_)) FIX _./ INV (_)/_)"  [1000,25,0,0,81] 71)

  "_Try_Catch":: "('a,'p,'f) com \<Rightarrow>('a,'p,'f) com \<Rightarrow> ('a,'p,'f) com"
        ("(0TRY (_)/ (2CATCH _)/ END)"  [0,0] 71)

  "_DoPre" :: "('a,'p,'f) com \<Rightarrow> ('a,'p,'f) com" 
  "_Do" :: "('a,'p,'f) com \<Rightarrow> bdy" ("(2DO/ (_)) /OD" [0] 1000)
  "_Lab":: "'a bexp \<Rightarrow> ('a,'p,'f) com \<Rightarrow> bdy"
            ("_\<bullet>/_" [1000,71] 81)
  "":: "bdy \<Rightarrow> ('a,'p,'f) com" ("_")
  "_Spec":: "pttrn \<Rightarrow> 's set \<Rightarrow>  ('s,'p,'f) com \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow> ('s,'p,'f) com"
            ("(ANNO _. _/ (_)/ _,/_)" [0,1000,20,1000,1000] 60)
  "_SpecNoAbrupt":: "pttrn \<Rightarrow> 's set \<Rightarrow>  ('s,'p,'f) com \<Rightarrow> 's set \<Rightarrow> ('s,'p,'f) com"
            ("(ANNO _. _/ (_)/ _)" [0,1000,20,1000] 60)
  "_LemAnno":: "'n \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com"
              ("(0 LEMMA (_)/ _ END)" [1000,0] 71)
  "_locnoinit"    :: "ident \<Rightarrow> locinit"               ("\<acute>_")
  "_locinit"      :: "[ident,'a] \<Rightarrow> locinit"          ("(2\<acute>_ :==/ _)")
  ""             :: "locinit \<Rightarrow> locinits"             ("_")
  "_locinits"    :: "[locinit, locinits] \<Rightarrow> locinits" ("_,/ _")
  "_Loc":: "[locinits,('s,'p,'f) com] \<Rightarrow> ('s,'p,'f) com"
                                         ("(2 LOC _;;/ (_) COL)" [0,0] 71)
  "_Switch":: "('s \<Rightarrow> 'v) \<Rightarrow> switchcases \<Rightarrow> ('s,'p,'f) com"
              ("(0 SWITCH (_)/ _ END)" [22,0] 71)
  "_switchcase":: "'v set \<Rightarrow> ('s,'p,'f) com \<Rightarrow> switchcase" ("_\<Rightarrow>/ _" )
  "_switchcasesSingle"  :: "switchcase \<Rightarrow> switchcases" ("_")         
  "_switchcasesCons":: "switchcase \<Rightarrow> switchcases \<Rightarrow> switchcases"
                       ("_/ | _") 
  "_Basic":: "basicblock \<Rightarrow> ('s,'p,'f) com" ("(0BASIC/ (_)/ END)" [22] 71)
  "_BasicBlock":: "basics \<Rightarrow> basicblock" ("_")
  "_BAssign"   :: "'b => 'b => basic"    ("(_ :==/ _)" [30, 30] 23)
  ""           :: "basic \<Rightarrow> basics"             ("_")
  "_basics"    :: "[basic, basics] \<Rightarrow> basics" ("_,/ _")

(* Experimental coloring for ProofGeneral; fails to run through latex*)
(*<*)
syntax (ProofGeneral output)
  "_guarantee"     :: "'s set \<Rightarrow> grd"       ("F_A" [1000] 1000)
  "_guaranteeStrip":: "'s set \<Rightarrow> grd"       ("B_A" [1000] 1000)
(*>*)

syntax (ascii)
  "_While_guard"       :: "grds => 'a bexp => bdy \<Rightarrow> ('a,'p,'f) com"
        ("(0WHILE (_|-> /_) /_)"  [0,0,1000] 71)
  "_While_guard_inv":: "grds\<Rightarrow>'a bexp\<Rightarrow>'a assn\<Rightarrow>bdy \<Rightarrow> ('a,'p,'f) com"
        ("(0WHILE (_|-> /_) INV (_) /_)"  [0,0,0,1000] 71)
  "_guards" :: "grds \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com" ("(_|->_ )" [60, 21] 23)


syntax (xsymbols)
  "_Assert"      :: "'a => 'a set"            ("(\<lbrace>_\<rbrace>)" [0] 1000)
  "_AssertState" :: "idt \<Rightarrow> 'a => 'a set"     ("(\<lbrace>_. _\<rbrace>)" [1000,0] 1000)

syntax (output)
  "_hidden_grds"      :: "grds" ("\<dots>")

translations
  "_Do c" => "c"
  "b\<bullet> c" => "condCatch c b SKIP"
  "b\<bullet> (_DoPre c)" <= "condCatch c b SKIP"
  "l\<bullet> (whileAnnoG gs b I V c)" <= "l\<bullet> (_DoPre (whileAnnoG gs b I V c))"
  "l\<bullet> (whileAnno b I V c)" <= "l\<bullet> (_DoPre (whileAnno b I V c))"
  "condCatch c b SKIP" <= "(_DoPre (condCatch c b SKIP))"
  "_Do c" <= "_DoPre c"
  "c;; d" == "Seq c d"
  "_guarantee g" => "(True,g)"
  "_guaranteeStrip g" == "guaranteeStripPair True g"
  "_grd g" => "(False,g)"
  "_grds g gs" => "g#gs"
  "_last_grd g" => "[g]"
  "_guards gs c" == "guards gs c"

  "SKIP" == "Language.com.Skip"
  "SKIP" <= "Skip"
  "SKIP" <= "Language.Skip"
  "SKIP" <= "com.Skip"
  "THROW" == "Throw"
  "{|s. P|}"                   == "{|\<acute>(op = s) \<and> P |}"
  "{|b|}"                   => "Collect (_quote b)"
  "IF b THEN c1 ELSE c2 FI" => "Cond {|b|} c1 c2"
  "IF b THEN c1 FI"         ==  "IF b THEN c1 ELSE SKIP FI"
  "IF\<^sub>g b THEN c1 FI"        ==  "IF\<^sub>g b THEN c1 ELSE SKIP FI"

  "_While_inv_var b I V c"          => "whileAnno {|b|} I V c"
  "_While_inv_var b I V (_DoPre c)" <= "whileAnno {|b|} I V c"
  "_While_inv b I c"                 == "_While_inv_var b I arbitrary c"
  "_While b c"                       == "_While_inv b {|arbitrary|} c"

  "_While_guard_inv_var gs b I V c"          => "whileAnnoG gs {|b|} I V c"
(*  "_While_guard_inv_var gs b I V (_DoPre c)" <= "whileAnnoG gs {|b|} I V c"*)
  "_While_guard_inv gs b I c"       == "_While_guard_inv_var gs b I arbitrary c"
  "_While_guard gs b c"             == "_While_guard_inv gs b {|arbitrary|} c"

  "_GuardedWhile_inv b I c"  == "_GuardedWhile_inv_var b I arbitrary c "
  "_GuardedWhile b c"        == "_GuardedWhile_inv b {|arbitrary|} c"
(*  "\<^bsup>s\<^esup>A"                      => "A s"*)
  "TRY c1 CATCH c2 END"     == "Catch c1 c2"
  "ANNO s. P c Q,A" => "specAnno (\<lambda>s. P) (\<lambda>s. c) (\<lambda>s. Q) (\<lambda>s. A)"
  "ANNO s. P c Q" == "ANNO s. P c Q,{}"

  "_WhileFix_inv_var b z I V c" => "whileAnnoFix {|b|} (\<lambda>z. I) (\<lambda>z. V) (\<lambda>z. c)"
  "_WhileFix_inv_var b z I V (_DoPre c)" <= "_WhileFix_inv_var {|b|} z I V c"
  "_WhileFix_inv b z I c" == "_WhileFix_inv_var b z I arbitrary c"

  "_GuardedWhileFix_inv b z I c" == "_GuardedWhileFix_inv_var b z I arbitrary c"

  "_GuardedWhileFix_inv_var b z I V c" =>
                         "_GuardedWhileFix_inv_var_hook {|b|} (\<lambda>z. I) (\<lambda>z. V) (\<lambda>z. c)"

  "_WhileFix_guard_inv_var gs b z I V c" => 
                                      "whileAnnoGFix gs {|b|} (\<lambda>z. I) (\<lambda>z. V) (\<lambda>z. c)"
  "_WhileFix_guard_inv_var gs b z I V (_DoPre c)" <= 
                                      "_WhileFix_guard_inv_var gs {|b|} z I V c"
  "_WhileFix_guard_inv gs b z I c" == "_WhileFix_guard_inv_var gs b z I arbitrary c"
  "LEMMA x c END" == "lem x c"
translations
 "(_switchcase V c)" => "(V,c)"
 "(_switchcasesSingle b)" => "[b]"
 "(_switchcasesCons b bs)" => "Cons b bs"
 "(_Switch v vs)" => "switch (_quote v) vs"


print_ast_translation {*
let
fun dest_abs (Appl [Constant "_abs",x,t]) = (x,t)
  | dest_abs _ = raise Match;
fun spec_tr' [P,c,Q,A] =
  let 
    val (x',P') = dest_abs P;
    val (_ ,c') = dest_abs c;
    val (_ ,Q') = dest_abs Q;
    val (_ ,A') = dest_abs A; 
  in if (A'=Constant "{}") 
     then Syntax.mk_appl (Constant "_SpecNoAbrupt") [x', P', c', Q'] 
     else Syntax.mk_appl (Constant "_Spec") [x', P', c', Q', A'] end;
fun whileAnnoFix_tr' [b,I,V,c] =
  let
    val (x',I') = dest_abs I;
    val (_ ,V') = dest_abs V;
    val (_ ,c') = dest_abs c;
  in Syntax.mk_appl (Constant "_WhileFix_inv_var") [b,x',I',V',c'] 
  end;
in [("specAnno",spec_tr'),
    ("whileAnnoFix",whileAnnoFix_tr')] 
end
*}



syntax
  "_faccess"  :: "'ref \<Rightarrow> ('ref \<Rightarrow> 'v) \<Rightarrow> 'v"
   ("_\<rightarrow>_" [65,1000] 100)

syntax (ascii)
  "_faccess"  :: "'ref \<Rightarrow> ('ref \<Rightarrow> 'v) \<Rightarrow> 'v"
   ("_->_" [65,1000] 100)

translations 

 "p\<rightarrow>f"        =>  "f p"
 "g\<rightarrow>(_antiquoteCur f)" <= "_antiquoteCur f g"


nonterminals par pars actuals

syntax 
  "_par" :: "'a \<Rightarrow> par"                                ("_")
  ""    :: "par \<Rightarrow> pars"                               ("_")
  "_pars" :: "[par,pars] \<Rightarrow> pars"                      ("_,/_")
  "_actuals" :: "pars \<Rightarrow> actuals"                      ("'(_')")
  "_actuals_empty" :: "actuals"                        ("'(')")

syntax "_Call" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)" ("CALL __" [1000,1000] 21)
       "_GuardedCall" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)" ("CALL\<^sub>g __" [1000,1000] 21)
       "_CallAss":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)" 
             ("_ :== CALL __" [30,1000,1000] 21)
       "_Proc" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)" ("PROC __" 21)
       "_ProcAss":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)" 
             ("_ :== PROC __" [30,1000,1000] 21)
       "_GuardedCallAss":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)" 
             ("_ :== CALL\<^sub>g __" [30,1000,1000] 21)
       "_DynCall" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)" ("DYNCALL __" [1000,1000] 21)
       "_GuardedDynCall" :: "'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)" ("DYNCALL\<^sub>g __" [1000,1000] 21)
       "_DynCallAss":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)" 
             ("_ :== DYNCALL __" [30,1000,1000] 21)
       "_GuardedDynCallAss":: "'a \<Rightarrow> 'p \<Rightarrow> actuals \<Rightarrow> (('a,string,'f) com)" 
             ("_ :== DYNCALL\<^sub>g __" [30,1000,1000] 21)

       "_Bind":: "['s \<Rightarrow> 'v, idt, 'v \<Rightarrow> ('s,'p,'f) com] \<Rightarrow> ('s,'p,'f) com" 
                      ("_ \<ggreater> _./ _" [22,1000,21] 21)
       "_bseq"::"('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com" 
           ("_\<ggreater>/ _" [22, 21] 21)
       "_FCall" :: "['p,actuals,idt,(('a,string,'f) com)]\<Rightarrow> (('a,string,'f) com)" 
                      ("CALL __ \<ggreater> _./ _" [1000,1000,1000,21] 21)



translations
"_Bind e i c" == "bind (_quote e) (\<lambda>i. c)"
"_FCall p acts i c" == "_FCall p acts (\<lambda>i. c)"
"_bseq c d" == "bseq c d"



nonterminals 
  modifyargs
syntax
  "_may_modify" :: "['a,'a,modifyargs] \<Rightarrow> bool" 
        ("_ may'_only'_modify'_globals _ in [_]" [100,100,0] 100)
  "_may_not_modify" :: "['a,'a] \<Rightarrow> bool"      
        ("_ may'_not'_modify'_globals _" [100,100] 100)
  "_may_modify_empty" :: "['a,'a] \<Rightarrow> bool"      
        ("_ may'_only'_modify'_globals _ in []" [100,100] 100)
  "_modifyargs" :: "[id,modifyargs] \<Rightarrow> modifyargs" ("_,/ _")
  ""            :: "id => modifyargs"              ("_")

translations
"s may_only_modify_globals Z in []" => "s may_not_modify_globals Z"


parse_translation (advanced){*
let
    val argsC = "_modifyargs";
    val updateN = "_update";
    val globalsN = "globals";
    val ex = "mex";
    val eq = "meq";
    val varn = HoarePackage.varname;

    fun extract_args (Const (argsC,_)$Free (n,_)$t) = varn n::extract_args t
      | extract_args (Free (n,_)) = [varn n]
      | extract_args t            = raise TERM ("extract_args", [t])

    fun idx [] y = error "idx: element not in list"
     |  idx (x::xs) y = if x=y then 0 else (idx xs y)+1

    fun gen_update ctxt names (name,t) = 
        HoareSyntax.update_comp (Context.Proof ctxt) [] false true name  (Bound (idx names name)) t

    fun gen_updates ctxt names t = Library.foldr (gen_update ctxt names) (names,t) 

    fun gen_ex (name,t) = Syntax.const ex $ Abs (name,dummyT,t)
 
    fun gen_exs names t = Library.foldr gen_ex (names,t)

  
    fun tr ctxt s Z names =
      let val upds = gen_updates ctxt (rev names) (Syntax.free globalsN$Z);
          val eq   = Syntax.const eq $ (Syntax.free globalsN$s) $ upds;
      in gen_exs names eq end;

    fun may_modify_tr ctxt [s,Z,names] = tr ctxt s Z 
                                           (sort_strings (extract_args names))
    fun may_not_modify_tr ctxt [s,Z] = tr ctxt s Z []
in [("_may_modify",may_modify_tr),("_may_not_modify",may_not_modify_tr)] end;
*}


print_translation {*
let
  val argsC = "_modifyargs";
  val chop = HoarePackage.chopsfx HoarePackage.deco;

  fun get_state ( _ $ _ $ t) = get_state t  (* for record-updates*)
    | get_state ( _ $ _ $ _ $ _ $ _ $ t) = get_state t (* for statespace-updates *)
    | get_state (globals$(s as Const ("_free",_) $ Free _)) = s
    | get_state (globals$(s as Const ("_bound",_) $ Free _)) = s
    | get_state (globals$(s as Const ("_var",_) $ Var _)) = s
    | get_state (globals$(s as Const _)) = s
    | get_state (globals$(s as Free _)) = s
    | get_state (globals$(s as Bound _)) = s
    | get_state t              = raise Match;

  fun mk_args [n] = Syntax.free (chop n)
    | mk_args (n::ns) = Syntax.const argsC $ Syntax.free (chop n) $ mk_args ns
    | mk_args _      = raise Match;

  fun tr' names (Abs (n,_,t)) = tr' (n::names) t
    | tr' names (Const ("mex",_) $ t) = tr' names t  
    | tr' names (Const ("meq",_) $ (globals$s) $ upd) =
          let val Z = get_state upd;
                
          in (case names of 
                [] => Syntax.const "_may_not_modify" $ s $ Z
              | xs => Syntax.const "_may_modify" $ s $ Z $ mk_args (rev names))
          end;

  fun may_modify_tr' [t] = tr' [] t
  fun may_not_modify_tr' [_$s,_$Z] = Syntax.const "_may_not_modify" $ s $ Z
in [("mex",may_modify_tr'),("meq",may_not_modify_tr')] end;
*}


(* decorate state components with suffix *)
(*
parse_ast_translation {*
 [("_Free",HoareSyntax.free_arg_ast_tr),
  ("_In",HoareSyntax.in_arg_ast_tr),
  ("_Where",HoareSyntax.where_arg_ast_tr "_Where"),
  ("_WhereElse",HoareSyntax.where_arg_ast_tr "_WhereElse")
] 
*}
*)
(*
parse_ast_translation (advanced) {*
 [("_antiquoteOld",HoareSyntax.antiquoteOld_varname_tr "_antiquoteOld")]
*}
*)


parse_translation {*
[("_antiquoteCur",HoareSyntax.antiquote_varname_tr "_antiquoteCur")]
*}


 parse_translation  (advanced) {*
[("_antiquoteOld",HoareSyntax.antiquoteOld_tr "_antiquoteOld"),
 ("_Call",HoareSyntax.call_tr false false),
 ("_FCall",HoareSyntax.fcall_tr),
 ("_CallAss",HoareSyntax.call_ass_tr false false),
 ("_GuardedCall",HoareSyntax.call_tr false true),
 ("_GuardedCallAss",HoareSyntax.call_ass_tr false true),
 ("_Proc",HoareSyntax.proc_tr),
 ("_ProcAss",HoareSyntax.proc_ass_tr),
 ("_DynCall",HoareSyntax.call_tr true false),
 ("_DynCallAss",HoareSyntax.call_ass_tr true false),
 ("_GuardedDynCall",HoareSyntax.call_tr true true),
 ("_GuardedDynCallAss",HoareSyntax.call_ass_tr true true),
 ("_BasicBlock",HoareSyntax.basic_assigns_tr)
]
*}

(*
  ("_Call",HoareSyntax.call_ast_tr),
  ("_CallAss",HoareSyntax.call_ass_ast_tr),
  ("_GuardedCall",HoareSyntax.guarded_call_ast_tr),
  ("_GuardedCallAss",HoareSyntax.guarded_call_ass_ast_tr)
*)

parse_translation (advanced) {*
  let
    fun quote_tr ctxt [t] = HoareSyntax.quote_tr ctxt "_antiquoteCur" t
      | quote_tr ctxt ts = raise TERM ("quote_tr", ts);
  in [("_quote", quote_tr)] end
*}



parse_translation (advanced) {*
  [("_Assign",HoareSyntax.assign_tr),
   ("_raise",HoareSyntax.raise_tr),
   ("_New",HoareSyntax.new_tr),
   ("_NNew",HoareSyntax.nnew_tr),
   ("_GuardedAssign",HoareSyntax.guarded_Assign_tr),
   ("_GuardedNew",HoareSyntax.guarded_New_tr),
   ("_GuardedNNew",HoareSyntax.guarded_NNew_tr),
   ("_GuardedWhile_inv_var",HoareSyntax.guarded_While_tr),
   ("_GuardedWhileFix_inv_var_hook",HoareSyntax.guarded_WhileFix_tr),
   ("_GuardedCond",HoareSyntax.guarded_Cond_tr),
   ("_Basic",HoareSyntax.basic_tr)]
*}

parse_translation (advanced) {*
 [("_Init",HoareSyntax.init_tr),
  ("_Loc",HoareSyntax.loc_tr)] 
*}


print_translation {*
    [("Basic", HoareSyntax.assign_tr'),
     ("raise", HoareSyntax.raise_tr'),
     ("Basic",HoareSyntax.new_tr'),
     ("Basic",HoareSyntax.init_tr'),
     ("Spec",HoareSyntax.nnew_tr'),
     ("block",HoareSyntax.loc_tr'),
     ("Collect",HoareSyntax.assert_tr'),
     ("Cond", HoareSyntax.bexp_tr' "_Cond"),
     ("switch",HoareSyntax.switch_tr'),
     ("guards",HoareSyntax.guards_tr'),
     ("whileAnnoG",HoareSyntax.whileAnnoG_tr'),
     ("whileAnnoGFix",HoareSyntax.whileAnnoGFix_tr'),
     ("Basic",HoareSyntax.basic_tr')]
*}


print_translation {*
let
fun spec_tr' ((coll as Const _)$
               ((splt as Const _) $ (t as (Abs (s,T,p))))::ts) =
  let fun selector (Const (c,T)) = HoareSyntax.is_state_var c
        | selector (Const ("_free",_)$(Free (c,T))) = HoareSyntax.is_state_var c
        | selector _             = false;
  in if HoareSyntax.antiquote_applied_only_to selector p
     then Syntax.const "Spec"$coll$(splt$HoareSyntax.quote_mult_tr' selector HoareSyntax.antiquoteCur HoareSyntax.antiquoteOld  (Abs (s,T,t)))
     else raise Match
  end
 | spec_tr' ts = raise Match
in [("Spec", spec_tr')] end
*}

syntax
"_Measure":: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<times> 'a) set"
      ("MEASURE _" [22] 1)
"_Mlex":: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
      (infixr "<*MLEX*>" 30)


translations
 "MEASURE f"       => "measure (_quote f)"
 "f <*MLEX*> r"       => "(_quote f) <*mlex*> r"



print_translation {*
let
fun selector (Const (c,T)) = HoareSyntax.is_state_var c  
    | selector _         = false;

fun measure_tr' ((t as (Abs (_,_,p)))::ts) =
     if HoareSyntax.antiquote_applied_only_to selector p
     then HoareSyntax.app_quote_tr' (Syntax.const "_Measure") (t::ts)
     else raise Match
 | measure_tr' _ = raise Match

fun mlex_tr' ((t as (Abs (_,_,p)))::r::ts) =
     if HoareSyntax.antiquote_applied_only_to selector p
     then HoareSyntax.app_quote_tr' (Syntax.const "_Mlex") (t::r::ts)
     else raise Match
 | mlex_tr' _ = raise Match

in [("measure",measure_tr'),("measure_lex_prod",mlex_tr')] end
*}


print_translation {*
    [("call", HoareSyntax.call_tr'),
     ("dynCall", HoareSyntax.dyn_call_tr'),
     ("fcall",HoareSyntax.fcall_tr'),
     ("bind",HoareSyntax.bind_tr')]
*}

print_translation (advanced) {*
    [("Call", HoareSyntax.proc_tr')]
*}


end