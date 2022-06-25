section \<open>List Syntax\<close>

theory List_Syntax imports Main begin

abbreviation list_member_syntax :: \<open>'a \<Rightarrow> 'a list \<Rightarrow> bool\<close> (\<open>_ [\<in>] _\<close> [51, 51] 50) where
  \<open>x [\<in>] A \<equiv> x \<in> set A\<close>

abbreviation list_not_member_syntax :: \<open>'a \<Rightarrow> 'a list \<Rightarrow> bool\<close> (\<open>_ [\<notin>] _\<close> [51, 51] 50) where
  \<open>x [\<notin>] A \<equiv> x \<notin> set A\<close>

abbreviation list_subset_syntax :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close> (\<open>_ [\<subset>] _\<close> [51, 51] 50) where
  \<open>A [\<subset>] B \<equiv> set A \<subset> set B\<close>

abbreviation list_subset_eq_syntax :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close> (\<open>_ [\<subseteq>] _\<close> [51, 51] 50) where
  \<open>A [\<subseteq>] B \<equiv> set A \<subseteq> set B\<close>

abbreviation removeAll_syntax :: \<open>'a list \<Rightarrow> 'a \<Rightarrow> 'a list\<close> (infix \<open>[\<div>]\<close> 75) where
  \<open>A [\<div>] x \<equiv> removeAll x A\<close>

syntax (ASCII)
  "_BallList"       :: \<open>pttrn \<Rightarrow> 'a list \<Rightarrow> bool \<Rightarrow> bool\<close>  (\<open>(3ALL (_/[:]_)./ _)\<close> [0, 0, 10] 10)
  "_BexList"        :: \<open>pttrn \<Rightarrow> 'a list \<Rightarrow> bool \<Rightarrow> bool\<close>  (\<open>(3EX (_/[:]_)./ _)\<close> [0, 0, 10] 10)
  "_Bex1List"       :: \<open>pttrn \<Rightarrow> 'a list \<Rightarrow> bool \<Rightarrow> bool\<close>  (\<open>(3EX! (_/[:]_)./ _)\<close> [0, 0, 10] 10)
  "_BleastList"     :: \<open>id \<Rightarrow> 'a list \<Rightarrow> bool \<Rightarrow> 'a\<close>       (\<open>(3LEAST (_/[:]_)./ _)\<close> [0, 0, 10] 10)

syntax (input)
  "_BallList"       :: \<open>pttrn \<Rightarrow> 'a list \<Rightarrow> bool \<Rightarrow> bool\<close>  (\<open>(3! (_/[:]_)./ _)\<close> [0, 0, 10] 10)
  "_BexList"        :: \<open>pttrn \<Rightarrow> 'a list \<Rightarrow> bool \<Rightarrow> bool\<close>  (\<open>(3? (_/[:]_)./ _)\<close> [0, 0, 10] 10)
  "_Bex1List"       :: \<open>pttrn \<Rightarrow> 'a list \<Rightarrow> bool \<Rightarrow> bool\<close>  (\<open>(3?! (_/[:]_)./ _)\<close> [0, 0, 10] 10)

syntax
  "_BallList"       :: \<open>pttrn \<Rightarrow> 'a list \<Rightarrow> bool \<Rightarrow> bool\<close>  (\<open>(3\<forall>(_/[\<in>]_)./ _)\<close> [0, 0, 10] 10)
  "_BexList"        :: \<open>pttrn \<Rightarrow> 'a list \<Rightarrow> bool \<Rightarrow> bool\<close>  (\<open>(3\<exists>(_/[\<in>]_)./ _)\<close> [0, 0, 10] 10)
  "_Bex1List"       :: \<open>pttrn \<Rightarrow> 'a list \<Rightarrow> bool \<Rightarrow> bool\<close>  (\<open>(3\<exists>!(_/[\<in>]_)./ _)\<close> [0, 0, 10] 10)
  "_BleastList"     :: \<open>id \<Rightarrow> 'a list \<Rightarrow> bool \<Rightarrow> 'a\<close>       (\<open>(3LEAST(_/[\<in>]_)./ _)\<close> [0, 0, 10] 10)

translations
  "\<forall>x[\<in>]A. P" \<rightleftharpoons> "CONST Ball (CONST set A) (\<lambda>x. P)"
  "\<exists>x[\<in>]A. P" \<rightleftharpoons> "CONST Bex (CONST set A) (\<lambda>x. P)"
  "\<exists>!x[\<in>]A. P" \<rightharpoonup> "\<exists>!x. x [\<in>] A \<and> P"
  "LEAST x[:]A. P" \<rightharpoonup> "LEAST x. x [\<in>] A \<and> P"

syntax (ASCII output)
  "_setlessAllList" :: \<open>[idt, 'a, bool] \<Rightarrow> bool\<close>  (\<open>(3ALL _[<]_./ _)\<close> [0, 0, 10] 10)
  "_setlessExList"  :: \<open>[idt, 'a, bool] \<Rightarrow> bool\<close>  (\<open>(3EX _[<]_./ _)\<close> [0, 0, 10] 10)
  "_setleAllList"   :: \<open>[idt, 'a, bool] \<Rightarrow> bool\<close>  (\<open>(3ALL _[<=]_./ _)\<close> [0, 0, 10] 10)
  "_setleExList"    :: \<open>[idt, 'a, bool] \<Rightarrow> bool\<close>  (\<open>(3EX _[<=]_./ _)\<close> [0, 0, 10] 10)
  "_setleEx1List"   :: \<open>[idt, 'a, bool] \<Rightarrow> bool\<close>  (\<open>(3EX! _[<=]_./ _)\<close> [0, 0, 10] 10)

syntax
  "_setlessAllList" :: \<open>[idt, 'a, bool] \<Rightarrow> bool\<close>   (\<open>(3\<forall>_[\<subset>]_./ _)\<close> [0, 0, 10] 10)
  "_setlessExList"  :: \<open>[idt, 'a, bool] \<Rightarrow> bool\<close>   (\<open>(3\<exists>_[\<subset>]_./ _)\<close> [0, 0, 10] 10)
  "_setleAllList"   :: \<open>[idt, 'a, bool] \<Rightarrow> bool\<close>   (\<open>(3\<forall>_[\<subseteq>]_./ _)\<close> [0, 0, 10] 10)
  "_setleExList"    :: \<open>[idt, 'a, bool] \<Rightarrow> bool\<close>   (\<open>(3\<exists>_[\<subseteq>]_./ _)\<close> [0, 0, 10] 10)
  "_setleEx1List"   :: \<open>[idt, 'a, bool] \<Rightarrow> bool\<close>   (\<open>(3\<exists>!_[\<subseteq>]_./ _)\<close> [0, 0, 10] 10)

translations
  "\<forall>A[\<subset>]B. P" \<rightharpoonup> "\<forall>A. A [\<subset>] B \<longrightarrow> P"
  "\<exists>A[\<subset>]B. P" \<rightharpoonup> "\<exists>A. A [\<subset>] B \<and> P"
  "\<forall>A[\<subseteq>]B. P" \<rightharpoonup> "\<forall>A. A [\<subseteq>] B \<longrightarrow> P"
  "\<exists>A[\<subseteq>]B. P" \<rightharpoonup> "\<exists>A. A [\<subseteq>] B \<and> P"
  "\<exists>!A[\<subseteq>]B. P" \<rightharpoonup> "\<exists>!A. A [\<subseteq>] B \<and> P"

end
