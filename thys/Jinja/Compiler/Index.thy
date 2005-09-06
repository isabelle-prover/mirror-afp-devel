(*  Title:      Jinja/Compiler/Index.thy
    ID:         $Id: Index.thy,v 1.2 2005-09-06 15:06:08 makarius Exp $
    Author:     Tobias Nipkow
    Copyright   TUM 2003
*)

header {* \isaheader{Indexing variables in variable lists} *}

theory Index imports  Main begin

text{* In order to support local variables and arbitrarily nested
blocks, the local variables are arranged as an indexed list. The
outermost local variable (``this'') is the first element in the list,
the most recently created local variable the last element. When
descending into a block structure, a corresponding list @{term Vs} of
variable names is maintained. To find the index of some variable
@{term V}, we have to find the index of the \emph{last} occurrence of
@{term V} in @{term Vs}. This is what @{term index} does: *}

consts
  index :: "'a list \<Rightarrow> 'a \<Rightarrow> nat"
primrec
  "index [] y = 0"
  "index (x#xs) y =
  (if x=y then if x \<in> set xs then index xs y + 1 else 0 else index xs y + 1)"

constdefs
  hidden :: "'a list \<Rightarrow> nat \<Rightarrow> bool"
  "hidden xs i  \<equiv>  i < size xs \<and> xs!i \<in> set(drop (i+1) xs)"

subsection {* @{term index} *}

lemma [simp]: "index (xs @ [x]) x = size xs"
(*<*)by(induct xs) simp_all(*>*)


lemma [simp]: "(index (xs @ [x]) y = size xs) = (x = y)"
(*<*)by(induct xs) auto(*>*)


lemma [simp]: "x \<in> set xs \<Longrightarrow> xs ! index xs x = x"
(*<*)by(induct xs) auto(*>*)


lemma [simp]: "x \<notin> set xs \<Longrightarrow> index xs x = size xs"
(*<*)by(induct xs) auto(*>*)


lemma index_size_conv[simp]: "(index xs x = size xs) = (x \<notin> set xs)"
(*<*)by(induct xs) auto(*>*)


lemma size_index_conv[simp]: "(size xs = index xs x) = (x \<notin> set xs)"
(*<*)by(induct xs) auto(*>*)


lemma "(index xs x < size xs) = (x \<in> set xs)"
(*<*)by(induct xs) auto(*>*)


lemma [simp]: "\<lbrakk> y \<in> set xs; x \<noteq> y \<rbrakk> \<Longrightarrow> index (xs @ [x]) y = index xs y"
(*<*)by(induct xs) auto(*>*)


lemma index_less_size[simp]: "x \<in> set xs \<Longrightarrow> index xs x < size xs"
(*<*)
apply(induct xs)
 apply simp
apply(fastsimp)
done
(*>*)

lemma index_less_aux: "\<lbrakk>x \<in> set xs; size xs \<le> n\<rbrakk> \<Longrightarrow> index xs x < n"
(*<*)
apply(subgoal_tac "index xs x < size xs")
apply(simp (no_asm_simp))
apply simp
done
(*>*)


lemma [simp]: "x \<in> set xs \<or> y \<in> set xs \<Longrightarrow> (index xs x = index xs y) = (x = y)"
(*<*)by (induct xs) auto(*>*)


lemma inj_on_index: "inj_on (index xs) (set xs)"
(*<*)by(simp add:inj_on_def)(*>*)


lemma index_drop: "\<And>x i. \<lbrakk> x \<in> set xs; index xs x < i \<rbrakk> \<Longrightarrow> x \<notin> set(drop i xs)"
(*<*)
apply(induct xs)
apply (auto simp:drop_Cons split:split_if_asm nat.splits dest:in_set_dropD)
done
(*>*)


subsection {* @{term hidden} *}

lemma hidden_index: "x \<in> set xs \<Longrightarrow> hidden (xs @ [x]) (index xs x)"
(*<*)
apply(auto simp add:hidden_def index_less_aux nth_append)
 apply(drule index_less_size)
 apply(simp del:index_less_size)
done
(*>*)


lemma hidden_inacc: "hidden xs i \<Longrightarrow> index xs x \<noteq> i"
(*<*)
apply(case_tac "x \<in> set xs")
apply(auto simp add:hidden_def index_less_aux nth_append index_drop)
done
(*>*)


lemma [simp]: "hidden xs i \<Longrightarrow> hidden (xs@[x]) i"
(*<*)by(auto simp add:hidden_def nth_append)(*>*)


lemma fun_upds_apply: "\<And>m ys.
  (m(xs[\<mapsto>]ys)) x =
  (let xs' = take (size ys) xs
   in if x \<in> set xs' then Some(ys ! index xs' x) else m x)"
(*<*)
apply(induct xs)
 apply (simp add:Let_def)
apply(case_tac ys)
 apply (simp add:Let_def)
apply (simp add:Let_def)
done
(*>*)


lemma map_upds_apply_eq_Some:
  "((m(xs[\<mapsto>]ys)) x = Some y) =
  (let xs' = take (size ys) xs
   in if x \<in> set xs' then ys ! index xs' x = y else m x = Some y)"
(*<*)by(simp add:fun_upds_apply Let_def)(*>*)


lemma map_upds_upd_conv_index:
  "\<lbrakk>x \<in> set xs; size xs \<le> size ys \<rbrakk>
  \<Longrightarrow> m(xs[\<mapsto>]ys)(x\<mapsto>y) = m(xs[\<mapsto>]ys[index xs x := y])"
(*<*)
apply(rule ext)
apply(simp add:fun_upds_apply index_less_aux eq_sym_conv Let_def)
done
(*>*)


end
