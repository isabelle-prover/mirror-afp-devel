(*  Title:       Jive Data and Store Model
    ID:          $Id: JML.thy,v 1.3 2005-09-06 15:06:08 makarius Exp $
    Author:      Norbert Schirmer <schirmer@informatik.tu-muenchen.de>  and  
                 Nicole Rauch <rauch@informatik.uni-kl.de>, 2005
    Maintainer:  Nicole Rauch <rauch@informatik.uni-kl.de>
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
