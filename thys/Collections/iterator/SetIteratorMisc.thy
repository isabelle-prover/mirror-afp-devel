(*  Title:       Auxiliary stuff for Iterators
    Author:      Thomas Tuerk <tuerk@in.tum.de>
    Maintainer:  Thomas Tuerk <tuerk@in.tum.de>
*)
header {* Auxiliary stuff *}
*** Obsolete
theory SetIteratorMisc
imports Main 
begin


subsection {* General Stuff *}

*** Called map_of_rev_distinct and declared as [simp] in Misc.thy
lemma map_of_rev : 
assumes "distinct (map fst xs)"
shows  "map_of (rev xs) = map_of xs"
using assms
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons kv xs)
  obtain k v where kv_eq[simp]: "kv = (k, v)" by (rule PairE)

  from Cons have ind_hyp: "map_of (rev xs) = map_of xs"
             and k_nin: "k \<notin> fst ` set xs"
    by (simp_all)

  show ?case
    by (simp add: fun_eq_iff ind_hyp map_add_Some_iff map_of_eq_None_iff k_nin
                  map_add_dom_app_simps)
qed


end


