(*     License:    LGPL  *)

section \<open>Preliminaries\<close>

subsection \<open>Formal definition of finite levels of the DCR hierarchy\<close>

theory Finite_DCR_Hierarchy
  imports Main
begin

subsubsection \<open>Auxiliary definitions\<close>

definition confl_rel
  where "confl_rel r \<equiv> (\<forall>a b c. (a,b) \<in> r^* \<and> (a,c) \<in> r^* \<longrightarrow> (\<exists> d. (b,d) \<in> r^* \<and> (c,d) \<in> r^*) )"

definition jn00 :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "jn00 r0 b c \<equiv> (\<exists> d. (b,d) \<in> r0^= \<and> (c,d) \<in> r0^=)"

definition jn01 :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "jn01 r0 r1 b c \<equiv> (\<exists>b' d. (b,b') \<in> r1^= \<and> (b',d) \<in> r0^* \<and> (c,d) \<in> r0^*)"

definition jn10 :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "jn10 r0 r1 b c \<equiv> (\<exists>c' d. (b,d) \<in> r0^* \<and> (c,c') \<in> r1^= \<and> (c',d) \<in> r0^*)"

definition jn11 :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "jn11 r0 r1 b c \<equiv> (\<exists>b' b'' c' c'' d.  (b,b') \<in> r0^* \<and> (b',b'') \<in> r1^= \<and> (b'',d) \<in> r0^* 
                                          \<and> (c,c') \<in> r0^* \<and> (c',c'') \<in> r1^= \<and> (c'',d) \<in> r0^*)"

definition jn02 :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "jn02 r0 r1 r2 b c \<equiv> (\<exists>b' d.  (b,b') \<in> r2^= \<and> (b',d) \<in> (r0 \<union> r1)^* \<and> (c,d) \<in> (r0 \<union> r1)^* )"

definition jn12 :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "jn12 r0 r1 r2 b c \<equiv> (\<exists>b' b'' d.  (b,b') \<in> (r0)^* \<and> (b',b'') \<in> r2^= \<and> (b'',d) \<in> (r0 \<union> r1)^* 
                                          \<and> (c,d) \<in> (r0 \<union> r1)^*)"

definition jn22 :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "jn22 r0 r1 r2 b c \<equiv> (\<exists>b' b'' c' c'' d.  (b,b') \<in> (r0 \<union> r1)^* \<and> (b',b'') \<in> r2^= \<and> (b'',d) \<in> (r0 \<union> r1)^* 
                                          \<and> (c,c') \<in> (r0 \<union> r1)^* \<and> (c',c'') \<in> r2^= \<and> (c'',d) \<in> (r0 \<union> r1)^*)"

definition LD2 :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> bool"
where
  "LD2 r r0 r1 \<equiv> ( r = r0 \<union> r1 
              \<and> (\<forall> a b c. (a,b) \<in> r0 \<and> (a,c) \<in> r0 \<longrightarrow> jn00 r0 b c)
              \<and> (\<forall> a b c. (a,b) \<in> r0 \<and> (a,c) \<in> r1 \<longrightarrow> jn01 r0 r1 b c)
              \<and> (\<forall> a b c. (a,b) \<in> r1 \<and> (a,c) \<in> r1 \<longrightarrow> jn11 r0 r1 b c) )"

definition LD3 :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> bool"
where
  "LD3 r r0 r1 r2 \<equiv> ( r = r0 \<union> r1 \<union> r2
              \<and> (\<forall> a b c. (a,b) \<in> r0 \<and> (a,c) \<in> r0 \<longrightarrow> jn00 r0 b c)
              \<and> (\<forall> a b c. (a,b) \<in> r0 \<and> (a,c) \<in> r1 \<longrightarrow> jn01 r0 r1 b c)
              \<and> (\<forall> a b c. (a,b) \<in> r1 \<and> (a,c) \<in> r1 \<longrightarrow> jn11 r0 r1 b c)
              \<and> (\<forall> a b c. (a,b) \<in> r0 \<and> (a,c) \<in> r2 \<longrightarrow> jn02 r0 r1 r2 b c)
              \<and> (\<forall> a b c. (a,b) \<in> r1 \<and> (a,c) \<in> r2 \<longrightarrow> jn12 r0 r1 r2 b c)
              \<and> (\<forall> a b c. (a,b) \<in> r2 \<and> (a,c) \<in> r2 \<longrightarrow> jn22 r0 r1 r2 b c))"

definition DCR2 :: "'a rel \<Rightarrow> bool"
where
  "DCR2 r \<equiv> ( \<exists>r0 r1. LD2 r r0 r1 )"

definition DCR3 :: "'a rel \<Rightarrow> bool"
where
  "DCR3 r \<equiv> ( \<exists>r0 r1 r2. LD3 r r0 r1 r2 )"

definition \<LL>1 :: "(nat \<Rightarrow> 'U rel) \<Rightarrow> nat \<Rightarrow> 'U rel"
where
  "\<LL>1 g \<alpha> \<equiv> \<Union> {A. \<exists> \<alpha>'. (\<alpha>' < \<alpha>) \<and> A = g \<alpha>'}"

definition \<LL>v :: "(nat \<Rightarrow> 'U rel) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'U rel"
where
  "\<LL>v g \<alpha> \<beta> \<equiv> \<Union> {A. \<exists> \<alpha>'. (\<alpha>' < \<alpha> \<or> \<alpha>' < \<beta>) \<and> A = g \<alpha>'}"

definition \<DD> :: "(nat \<Rightarrow> 'U rel) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('U \<times> 'U \<times> 'U \<times> 'U) set"
where
  "\<DD> g \<alpha> \<beta> = {(b,b',b'',d). (b,b') \<in> (\<LL>1 g \<alpha>)^* \<and> (b',b'') \<in> (g \<beta>)^= \<and> (b'',d) \<in> (\<LL>v g \<alpha> \<beta>)^*}"

definition DCR_generating :: "(nat \<Rightarrow> 'U rel) \<Rightarrow> bool"
where
  "DCR_generating g \<equiv> (\<forall> \<alpha> \<beta> a b c. (a,b) \<in> (g \<alpha>) \<and> (a,c) \<in> (g \<beta>)
             \<longrightarrow>  (\<exists> b' b'' c' c'' d. (b,b',b'',d) \<in> (\<DD> g \<alpha> \<beta>) \<and> (c,c',c'',d) \<in> (\<DD> g \<beta> \<alpha>) ))"

subsubsection \<open>Result\<close>

text \<open>The next definition formalizes the condition ``an ARS with a reduction relation $r$ belongs to the class $DCR_n$'', where $n$ is a natural number.\<close>

definition DCR :: "nat \<Rightarrow> 'U rel \<Rightarrow> bool"
where
  "DCR n r \<equiv> (\<exists> g::(nat \<Rightarrow> 'U rel). DCR_generating g \<and> r = \<Union> { r'. \<exists> \<alpha>'. \<alpha>' < n \<and> r' = g \<alpha>' } )"

end
