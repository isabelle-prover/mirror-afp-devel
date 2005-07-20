(*  Title:       Jive Data and Store Model
    ID:          $Id: JML.thy,v 1.2 2005-07-20 05:09:06 lsf37 Exp $
    Author:      Norbert Schirmer <schirmer@informatik.tu-muenchen.de>  and  
                 Nicole Rauch <rauch@informatik.uni-kl.de>, 2005
    Maintainer:  Nicole Rauch <rauch@informatik.uni-kl.de>
    License:     LGPL
*)

header {* The Formalization of JML Operators *}

theory JML = StoreProperties :

text {* JML operators that are to be used in Hoare formulae can be formalized here.
*}

constdefs
  instanceof :: "Value \<Rightarrow> Javatype \<Rightarrow> bool"  ("_ @instanceof _")
  "instanceof v t \<equiv> typeof v \<le> t"

end
