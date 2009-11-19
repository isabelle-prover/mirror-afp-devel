header {* \isaheader{The state} *}

theory State imports Com begin


datatype lift_var = Loc vname | ReturnProc | ReturnLabel

types call_frame = "lift_var \<rightharpoonup> val"

fun "interpret" :: "expr \<Rightarrow> call_frame \<Rightarrow> val option"
where Val: "interpret (Val v) cf = Some v"
  | Var: "interpret (Var V) cf = cf (Loc V)"
  | BinOp: "interpret (e\<^isub>1\<guillemotleft>bop\<guillemotright>e\<^isub>2) cf = 
    (case interpret e\<^isub>1 cf of None \<Rightarrow> None
                         | Some v\<^isub>1 \<Rightarrow> (case interpret e\<^isub>2 cf of None \<Rightarrow> None
                                                           | Some v\<^isub>2 \<Rightarrow> (
      case binop bop v\<^isub>1 v\<^isub>2 of None \<Rightarrow> None | Some v \<Rightarrow> Some v)))"


abbreviation update :: "call_frame \<Rightarrow> vname \<Rightarrow> expr \<Rightarrow> call_frame"
  where "update cf V e \<equiv> cf(Loc V:=(interpret e cf))"

abbreviation state_check :: "call_frame \<Rightarrow> expr \<Rightarrow> val option \<Rightarrow> bool"
where "state_check cf b v \<equiv> (interpret b cf = v)"


abbreviation set_params :: "nat \<Rightarrow> nat \<Rightarrow> expr list \<Rightarrow> (call_frame \<Rightarrow> val option) list"
  where "set_params i l es \<equiv> (\<lambda>cf. Some (Intg (int i)))#(\<lambda>cf. Some (Intg (int l)))#
  (map (\<lambda>e cf. interpret e cf) es)"

abbreviation correct_return :: "nat \<Rightarrow> nat \<Rightarrow> call_frame \<Rightarrow> bool"
  where "correct_return i l \<equiv> 
  (\<lambda>cf. cf ReturnProc = Some(Intg (int i)) \<and> cf ReturnLabel = Some(Intg (int l)))"

end