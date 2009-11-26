header {* \isaheader{The state} *}

theory State imports Com begin

fun "interpret" :: "expr \<Rightarrow> (vname \<rightharpoonup> val) \<Rightarrow> val option"
where Val: "interpret (Val v) cf = Some v"
  | Var: "interpret (Var V) cf = cf V"
  | BinOp: "interpret (e\<^isub>1\<guillemotleft>bop\<guillemotright>e\<^isub>2) cf = 
    (case interpret e\<^isub>1 cf of None \<Rightarrow> None
                         | Some v\<^isub>1 \<Rightarrow> (case interpret e\<^isub>2 cf of None \<Rightarrow> None
                                                           | Some v\<^isub>2 \<Rightarrow> (
      case binop bop v\<^isub>1 v\<^isub>2 of None \<Rightarrow> None | Some v \<Rightarrow> Some v)))"


abbreviation update :: "(vname \<rightharpoonup> val) \<Rightarrow> vname \<Rightarrow> expr \<Rightarrow> (vname \<rightharpoonup> val)"
  where "update cf V e \<equiv> cf(V:=(interpret e cf))"

abbreviation state_check :: "(vname \<rightharpoonup> val) \<Rightarrow> expr \<Rightarrow> val option \<Rightarrow> bool"
where "state_check cf b v \<equiv> (interpret b cf = v)"

end