section "Stack Proofs"

theory Stack_Proof
imports Stack_Aux RTD_Util
begin

lemma push_list [simp]: "list (push x stack) = x # list stack"
  by(cases stack) auto

lemma pop_list [simp]: "list (pop stack) = tl (list stack)"
  by(induction stack rule: pop.induct) auto

lemma first_list [simp]: "\<not> is_empty stack \<Longrightarrow> first stack = hd (list stack)"
  by(induction stack rule: first.induct) auto

lemma list_empty: "list stack = [] \<longleftrightarrow> is_empty stack"
  by(induction stack rule: is_empty_stack.induct) auto

lemma list_not_empty: "list stack  \<noteq> [] \<longleftrightarrow> \<not> is_empty stack"
  by(induction stack rule: is_empty_stack.induct) auto 

lemma list_empty_2 [simp]: "\<lbrakk>list stack \<noteq> []; is_empty stack\<rbrakk> \<Longrightarrow> False"
  by (simp add: list_empty)

lemma list_not_empty_2 [simp]:"\<lbrakk>list stack = []; \<not> is_empty stack\<rbrakk> \<Longrightarrow> False"
  by (simp add: list_empty)

lemma list_empty_size: "list stack = [] \<longleftrightarrow> size stack = 0"
  by(induction stack) auto 

lemma list_not_empty_size:"list stack \<noteq> [] \<longleftrightarrow> 0 < size stack"
  by(induction stack) auto

lemma list_empty_size_2 [simp]: "\<lbrakk>list stack \<noteq> []; size stack = 0\<rbrakk> \<Longrightarrow> False"
  by (simp add: list_empty_size) 

lemma list_not_empty_size_2 [simp]:"\<lbrakk>list stack = []; 0 < size stack\<rbrakk> \<Longrightarrow> False"
  by (simp add: list_empty_size)

lemma size_push [simp]: "size (push x stack) = Suc (size stack)"
  by(cases stack) auto

lemma size_pop [simp]: "size (pop stack) = size stack - Suc 0"
  by(induction stack rule: pop.induct) auto

lemma size_empty: "size (stack :: 'a stack) = 0 \<longleftrightarrow> is_empty stack"
  by(induction stack rule: is_empty_stack.induct) auto

lemma size_not_empty: "size (stack :: 'a stack) > 0 \<longleftrightarrow> \<not> is_empty stack"
  by(induction stack rule: is_empty_stack.induct) auto

lemma size_empty_2[simp]: "\<lbrakk>size (stack :: 'a stack) = 0; \<not>is_empty stack\<rbrakk> \<Longrightarrow> False"
  by (simp add: size_empty)

lemma size_not_empty_2[simp]: "\<lbrakk>0 < size (stack :: 'a stack); is_empty stack\<rbrakk> \<Longrightarrow> False"
  by (simp add: size_not_empty)

lemma size_list_length [simp]: "length (list stack) = size stack"
  by(cases stack) auto

lemma first_pop [simp]: "\<not> is_empty stack \<Longrightarrow> first stack # list (pop stack) = list stack"
  by(induction stack rule: pop.induct) auto

lemma push_not_empty [simp]: "\<lbrakk>\<not> is_empty stack; is_empty (push x stack)\<rbrakk> \<Longrightarrow> False"
  by(induction x stack rule: push.induct) auto

lemma pop_list_length [simp]: "\<not> is_empty stack
   \<Longrightarrow> Suc (length (list (pop stack))) = length (list stack)"
  by(induction stack rule: pop.induct) auto

lemma first_take: "\<not>is_empty stack \<Longrightarrow> [first stack] = take 1 (list stack)"
  by (simp add: list_empty)

lemma first_take_tl [simp]: "0 < size big
   \<Longrightarrow> (first big # take count (tl (list big))) = take (Suc count) (list big)"
  by(induction big rule: Stack.first.induct) auto

lemma first_take_pop [simp]: "\<lbrakk>\<not>is_empty stack; 0 < x\<rbrakk>
   \<Longrightarrow> first stack # take (x - Suc 0) (list (pop stack)) = take x (list stack)"
  by(induction stack rule: pop.induct) (auto simp: take_Cons')

lemma [simp]: "first (Stack [] []) = undefined"
  by (meson first.elims list.distinct(1) stack.inject)

lemma first_hd: "first stack = hd (list stack)"
  by(induction stack rule: first.induct)(auto simp: hd_def)

lemma pop_tl [simp]: "list (pop stack) = tl (list stack)" 
  by(induction stack rule: pop.induct) auto

lemma pop_drop: "list (pop stack) = drop 1 (list stack)" 
  by (simp add: drop_Suc)

lemma popN_drop [simp]: "list ((pop ^^ n) stack) = drop n (list stack)" 
  by(induction n)(auto simp: drop_Suc tl_drop)

lemma popN_size [simp]: "size ((pop ^^ n) stack) = (size stack) - n"
 by(induction n) auto

lemma take_first: "\<lbrakk>0 < size s1; 0 < size s2; take (size s1) (list s2) = take (size s2) (list s1)\<rbrakk>
    \<Longrightarrow> first s1 = first s2"
  by(induction s1 rule: first.induct; induction s2 rule: first.induct) auto

end
