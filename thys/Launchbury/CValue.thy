theory CValue
imports C
begin

domain CValue' = CFn (lazy "(C \<rightarrow> CValue') \<rightarrow> (C \<rightarrow> CValue')")
type_synonym CValue = "C \<rightarrow> CValue'"

fixrec CFn_project :: "CValue' \<rightarrow> CValue \<rightarrow> CValue"
 where "CFn_project\<cdot>(CFn\<cdot>f)\<cdot>v = f \<cdot> v"

abbreviation CFn_project_abbr (infix "\<down>CFn" 55)
  where "f \<down>CFn v \<equiv> CFn_project\<cdot>f\<cdot>v"

lemma CFn_project_strict[simp]:
  "\<bottom> \<down>CFn v = \<bottom>"
  by (fixrec_simp) 

text {* HOLCF provides us @{const CValue'_take}@{text "::"}@{typeof CValue'_take};
we want a similar function for @{typ CValue}. *}

abbreviation CValue_take where "CValue_take n \<equiv> cfun_map\<cdot>ID\<cdot>(CValue'_take n)"

lemma CValue_chain_take: "chain CValue_take"
  by (auto intro: chainI cfun_belowI chainE[OF CValue'.chain_take] monofun_cfun_fun)

lemma CValue_reach: "(\<Squnion> n. CValue_take n\<cdot>x) = x"
  by (auto intro:  cfun_eqI simp add: contlub_cfun_fun[OF ch2ch_Rep_cfunL[OF CValue_chain_take]]  CValue'.reach)


end
