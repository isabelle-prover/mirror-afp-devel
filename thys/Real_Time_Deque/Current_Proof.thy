section "Current Proofs"

theory Current_Proof
imports Current_Aux Stack_Proof
begin

lemma push_list [simp]: "list (push x current) = x # list current"
  by(induction x current rule: push.induct) auto

lemma pop_list [simp]: 
    "\<lbrakk>0 < size current; invar current\<rbrakk> \<Longrightarrow> fst (pop current) # tl (list current) = list current"
  by(induction current rule: pop.induct)(auto simp: size_not_empty list_not_empty)

lemma drop_first_list [simp]: "\<lbrakk>invar current; 0 < size current\<rbrakk>
  \<Longrightarrow> list (drop_first current) = tl (list current)"
  by(induction current rule: pop.induct)(auto simp: drop_Suc)

lemma invar_push: "invar current \<Longrightarrow> invar (push x current)"
  by(induction x current rule: push.induct) auto

lemma invar_pop: "\<lbrakk>0 < size current; invar current; pop current = (x, current')\<rbrakk>
   \<Longrightarrow> invar current'"
  by(induction current arbitrary: x rule: pop.induct) auto

lemma invar_drop_first: "\<lbrakk>0 < size current; invar current\<rbrakk> \<Longrightarrow> invar (drop_first current)"
  using invar_pop
  by (metis eq_snd_iff)

lemma list_size [simp]: "\<lbrakk>invar current; list current = []; 0 < size current\<rbrakk> \<Longrightarrow> False"
  by(induction current)(auto simp: size_not_empty list_empty)

lemma size_new_push [simp]: "invar current \<Longrightarrow> size_new (push x current) = Suc (size_new current)"
  by(induction x current rule: push.induct) auto

lemma size_push [simp]: "size (push x current) = Suc (size current)"
  by(induction x current rule: push.induct) auto

lemma size_new_pop [simp]: "\<lbrakk>0 < size_new current; invar current \<rbrakk>
  \<Longrightarrow> Suc (size_new (drop_first current)) = size_new current"
  by(induction current rule: pop.induct) auto

lemma size_pop [simp]: "\<lbrakk>0 < size current; invar current \<rbrakk>
   \<Longrightarrow> Suc (size (drop_first current)) = size current"
  by(induction current rule: pop.induct) auto

lemma size_pop_suc [simp]: "\<lbrakk>0 < size current; invar current; pop current = (x, current') \<rbrakk>
   \<Longrightarrow> Suc (size current') = size current"
  by(induction current rule: pop.induct) auto

lemma size_pop_sub: "\<lbrakk>0 < size current; invar current; pop current = (x, current') \<rbrakk>
   \<Longrightarrow> size current' = size current - 1"
  by(induction current rule: pop.induct) auto

lemma size_drop_first_sub: "\<lbrakk>0 < size current; invar current \<rbrakk>
   \<Longrightarrow> size (drop_first current) = size current - 1"
  by(induction current rule: pop.induct) auto

end