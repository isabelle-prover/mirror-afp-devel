(* Author: Tobias Nipkow *)

header {* Weak well-formedness of CoreC++ programs *}

theory WWellForm imports WellForm Expr begin

constdefs
  wwf_mdecl :: "prog \<Rightarrow> cname \<Rightarrow> mdecl \<Rightarrow> bool"
  "wwf_mdecl P C  \<equiv>  \<lambda>(M,Ts,T,(pns,body)).
  length Ts = length pns \<and> distinct pns \<and> this \<notin> set pns \<and> fv body \<subseteq> {this} \<union> set pns"

lemma wwf_mdecl[simp]:
  "wwf_mdecl P C (M,Ts,T,pns,body) =
  (length Ts = length pns \<and> distinct pns \<and> this \<notin> set pns \<and> fv body \<subseteq> {this} \<union> set pns)"
by(simp add:wwf_mdecl_def)


syntax
  wwf_prog :: "prog \<Rightarrow> bool"
translations
  "wwf_prog"  ==  "wf_prog wwf_mdecl"

end
