section  \<open>Double-Ended Queue Specification\<close>

theory Deque
imports Main
begin

text \<open>Model-oriented specification in terms of an abstraction function to a list.\<close>

locale Deque =
fixes empty :: "'q"
fixes enqL :: "'a \<Rightarrow> 'q \<Rightarrow> 'q"
fixes enqR :: "'a \<Rightarrow> 'q \<Rightarrow> 'q"
fixes firstL :: "'q \<Rightarrow> 'a"
fixes firstR :: "'q \<Rightarrow> 'a"
fixes deqL :: "'q \<Rightarrow> 'q"
fixes deqR :: "'q \<Rightarrow> 'q"
fixes is_empty :: "'q \<Rightarrow> bool"
fixes listL :: "'q \<Rightarrow> 'a list"
fixes invar :: "'q \<Rightarrow> bool"

assumes list_empty:
 "listL empty = []"

assumes list_enqL:   
 "invar q \<Longrightarrow> listL(enqL x q) = x # listL q"
assumes list_enqR:  
 "invar q \<Longrightarrow> rev (listL (enqR x q)) = x # rev (listL q)"
assumes list_deqL:   
 "\<lbrakk>invar q; \<not> listL q = []\<rbrakk> \<Longrightarrow> listL(deqL q) = tl(listL q)"
assumes list_deqR: 
 "\<lbrakk>invar q; \<not> rev (listL q) = []\<rbrakk> \<Longrightarrow> rev (listL (deqR q)) = tl (rev (listL q))"

assumes list_firstL:
 "\<lbrakk>invar q; \<not> listL q = []\<rbrakk> \<Longrightarrow> firstL q = hd(listL q)"
assumes list_firstR:
 "\<lbrakk>invar q; \<not> rev (listL q) = []\<rbrakk> \<Longrightarrow> firstR q = hd(rev(listL q))"

assumes list_is_empty:  
 "invar q \<Longrightarrow> is_empty q = (listL q = [])"

assumes invar_empty: 
 "invar empty"

assumes invar_enqL:  
 "invar q \<Longrightarrow> invar(enqL x q)"
assumes invar_enqR: 
 "invar q \<Longrightarrow> invar(enqR x q)"
assumes invar_deqL: 
 "\<lbrakk>invar q; \<not> is_empty q\<rbrakk>  \<Longrightarrow> invar(deqL q)"
assumes invar_deqR: 
 "\<lbrakk>invar q; \<not> is_empty q\<rbrakk>  \<Longrightarrow> invar(deqR q)"
begin

abbreviation listR :: "'q \<Rightarrow> 'a list" where
  "listR deque \<equiv> rev (listL deque)"

end



end
