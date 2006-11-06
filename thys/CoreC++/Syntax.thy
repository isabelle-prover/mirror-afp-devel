(*  Title:       CoreC++
    ID:          $Id: Syntax.thy,v 1.6 2006-11-06 11:54:13 wasserra Exp $
    Author:      Tobias Nipkow, Daniel Wasserrab 
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

    Extracted from the Jinja theory J/Expr.thy by Tobias Nipkow
*)


header {* \isaheader{Syntax} *}

theory Syntax imports Exceptions begin


text{*Syntactic sugar*}

syntax
  InitBlock:: "vname \<Rightarrow> ty \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"   ("(1'{_:_ := _;/ _})")
translations
  "InitBlock V T e1 e2" => "{V:T; V := e1;; e2}"

syntax
 unit  :: expr
 null  :: expr
 ref   :: "reference \<Rightarrow> expr"
 true  :: expr
 false :: expr
translations
 "unit" == "Val Unit"
 "null" == "Val Null"
 "ref r" == "Val(Ref r)"
 "true" == "Val(Bool True)"
 "false" == "Val(Bool False)"

syntax
  Throw :: "reference \<Rightarrow> expr"
  THROW :: "cname \<Rightarrow> expr"
translations
  "Throw r" == "throw(ref r)"
  "THROW xc" => "Throw(addr_of_sys_xcpt xc,[xc])"


end
