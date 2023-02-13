section "Idle Proofs"

theory Idle_Proof
  imports Idle_Aux Stack_Proof
begin

lemma push_list [simp]: "list (push x idle) = x # list idle"
  by(induction idle arbitrary: x) auto

lemma pop_list [simp]: "\<lbrakk>\<not> is_empty idle; pop idle = (x, idle')\<rbrakk> \<Longrightarrow> x # list idle' = list idle"
  by(induction idle arbitrary: x)(auto simp: list_not_empty)

lemma pop_list_tl [simp]: 
    "\<lbrakk>\<not> is_empty idle; pop idle = (x, idle')\<rbrakk> \<Longrightarrow> x # (tl (list idle)) = list idle" 
  by(induction idle arbitrary: x) (auto simp: list_not_empty)

lemma pop_list_tl' [simp]: "\<lbrakk>pop idle = (x, idle')\<rbrakk> \<Longrightarrow> list idle' = tl (list idle)"
  by(induction idle arbitrary: x)(auto simp: drop_Suc)

lemma size_push [simp]: "size (push x idle) = Suc (size idle)"
  by(induction idle arbitrary: x) auto

lemma size_pop [simp]: "\<lbrakk>\<not>is_empty idle; pop idle = (x, idle')\<rbrakk> \<Longrightarrow> Suc (size idle') = size idle"
  by(induction idle arbitrary: x)(auto simp: size_not_empty)

lemma size_pop_sub: "\<lbrakk>pop idle = (x, idle')\<rbrakk> \<Longrightarrow> size idle' = size idle - 1"
  by(induction idle arbitrary: x) auto

lemma invar_push: "invar idle \<Longrightarrow> invar (push x idle)"
  by(induction x idle rule: push.induct) auto

lemma invar_pop: "\<lbrakk>invar idle; pop idle = (x, idle')\<rbrakk> \<Longrightarrow> invar idle'"
  by(induction idle arbitrary: x rule: pop.induct) auto

lemma size_empty: "size idle = 0 \<longleftrightarrow> is_empty (idle :: 'a idle)"
  by(induction idle)(auto simp: size_empty)

lemma size_not_empty: "0 < size idle \<longleftrightarrow> \<not>is_empty (idle :: 'a idle)"
  by(induction idle)(auto simp: size_not_empty)

lemma size_empty_2 [simp]: "\<lbrakk>\<not>is_empty (idle :: 'a idle); 0 = size idle\<rbrakk> \<Longrightarrow> False" 
  by (simp add: size_empty)

lemma size_not_empty_2 [simp]: "\<lbrakk>is_empty (idle :: 'a idle); 0 < size idle\<rbrakk> \<Longrightarrow> False" 
  by (simp add: size_not_empty)

lemma list_empty: "list idle = [] \<longleftrightarrow> is_empty idle"
  by(induction idle)(simp add: list_empty)

lemma list_not_empty: "list idle  \<noteq> [] \<longleftrightarrow> \<not> is_empty idle"
  by(induction idle)(simp add: list_not_empty)

lemma list_empty_2 [simp]: "\<lbrakk>list idle = []; \<not>is_empty (idle :: 'a idle)\<rbrakk> \<Longrightarrow> False" 
  using list_empty by blast

lemma list_not_empty_2 [simp]: "\<lbrakk>list idle \<noteq> []; is_empty (idle :: 'a idle)\<rbrakk> \<Longrightarrow> False" 
  using list_not_empty by blast

lemma list_empty_size: "list idle = [] \<longleftrightarrow> 0 = size idle"
  by (simp add: list_empty size_empty)

lemma list_not_empty_size: "list idle \<noteq> [] \<longleftrightarrow> 0 < size idle"
  by (simp add: list_empty_size)

lemma list_empty_size_2 [simp]: "\<lbrakk>list idle \<noteq> []; 0 = size idle\<rbrakk> \<Longrightarrow> False" 
  by (simp add: list_empty size_empty)

lemma list_not_empty_size_2 [simp]: "\<lbrakk>list idle = []; 0 < size idle\<rbrakk> \<Longrightarrow> False" 
  by (simp add: list_empty_size)

end
