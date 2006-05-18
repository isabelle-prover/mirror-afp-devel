(*  Title:       Jive Data and Store Model
    ID:          $Id: JML.thy,v 1.4 2006-05-18 14:19:23 lsf37 Exp $
    Author:      Norbert Schirmer <schirmer at informatik.tu-muenchen.de>  and  
                 Nicole Rauch <rauch at informatik.uni-kl.de>, 2005
    Maintainer:  Nicole Rauch <rauch at informatik.uni-kl.de>
    License:     LGPL
*)

header {* The Formalization of JML Operators *}

theory JML imports StoreProperties  begin

text {* JML operators that are to be used in Hoare formulae can be formalized here.
*}

constdefs
  instanceof :: "Value \<Rightarrow> Javatype \<Rightarrow> bool"  ("_ @instanceof _")
  "instanceof v t \<equiv> typeof v \<le> t"

end
