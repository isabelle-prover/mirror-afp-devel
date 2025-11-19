section \<open> Examples of Shallow Expressions \<close>

theory Shallow_Expressions_Examples
  imports Shallow_Expressions
begin

subsection \<open> Basic Expressions and Queries \<close>

text \<open> We define some basic variables using the @{command alphabet} command, process some simple
  expressions, and then perform some unrestriction queries and substitution transformations. \<close>

declare [[literal_variables]]

alphabet st =
  v1 :: int
  v2 :: int
  v3 :: string

term "(v1 > a)\<^sub>e"

declare [[pretty_print_exprs=false]]

term "(v1 > a)\<^sub>e"

declare [[pretty_print_exprs]]

lemma "$v2 \<sharp> (v1 > 5)\<^sub>e"
  by unrest

lemma "(v1 > 5)\<^sub>e\<lbrakk>v2/v1\<rbrakk> = (v2 > 5)\<^sub>e"
  by subst_eval 

text \<open> We sometimes would like to define ``constructors'' for expressions. These are functions that
  produce expressions, and may also have expressions as arguments. Unlike for other functions,
  during lifting the state is not passed to the arguments, but is passed to the constructor
  constant itself. An example is given below: \<close>

definition v1_greater :: "int \<Rightarrow> (bool, st) expr" where
"v1_greater x = (v1 > x)\<^sub>e"

expr_constructor v1_greater

text \<open> Definition @{const v1_greater} is a constructor for an expression, and so it should not
  be lifted. Therefore we use the command @{command expr_constructor} to specify this, which
  modifies the behaviour of the lifting parser, and means that @{term "(v1_greater 7)\<^sub>e"} is 
  correctly translated. 

  If it is desired that one or more of the arguments is an expression, then this can be specified 
  using an optional list of numbers. In the example below, the first argument is an expression. \<close>

definition v1_greater' :: "(int, st) expr \<Rightarrow> (bool, st) expr" where
"v1_greater' x = (v1 > @x)\<^sub>e"

expr_constructor v1_greater' (0)

term "(v1_greater' (v1 + 1))\<^sub>e"

text \<open> We also sometimes wish to have functions that return expressions, whose arguments should be 
  lifted. We can achieve this using the @{command expr_function} command: \<close>

definition v1_less :: "int \<Rightarrow> (bool, st) expr" where
"v1_less x = (v1 < x)\<^sub>e"

expr_function v1_less

text \<open> This means, we can parse terms like @{term "(v1_less (v1 + 1))\<^sub>e"} -- notice that this returns
  an expression and takes an expression as an input. Alternatively, we can achieve the same effect
  with the @{command edefinition} command, which is like @{command definition}, but uses the expression
  parse and lifts the arguments as expressions. It is typically used for user-level functions that
  depend on the state. \<close>

edefinition v1_less' where "v1_less' x = (v1 < x)"

term "(v1_less' (v1 + 1))\<^sub>e"

text \<open> In addition, we can define an expression using the command below, which automatically performs 
  expression lifting in the defining term. These constants are also set as expression constructors. \<close>

expression v1_is_big over st is "v1 > 100"

expression inc_v1 over "st \<times> st" is "v1\<^sup>> = v1\<^sup>< + 1"

text \<open> Definitional equations for named expressions are collected in the theorem attribute 
  @{thm named_expr_defs}. \<close>

thm named_expr_defs

subsection \<open> Hierarchical State \<close>

alphabet person =
  name :: string
  age  :: nat

alphabet company =
  adam :: person
  bella :: person
  carol :: person

term "($adam:age > $carol:age)\<^sub>e"

term "($adam:name \<noteq> $bella:name)\<^sub>e"

subsection \<open> Program Semantics \<close>

text \<open> We give a predicative semantics to a simple imperative programming language with sequence,
  conditional, and assignment, using lenses and shallow expressions. We then use these definitions
  to prove some basic laws of programming. \<close>

declare [[literal_variables=false]]

type_synonym 's prog = "'s \<times> 's \<Rightarrow> bool"

definition seq :: "'s prog \<Rightarrow> 's prog \<Rightarrow> 's prog" (infixr ";;" 85) where
[expr_defs]: "seq P Q = (\<exists> s. P\<lbrakk>\<guillemotleft>s\<guillemotright>/\<^bold>v\<^sup>>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>s\<guillemotright>/\<^bold>v\<^sup><\<rbrakk>)\<^sub>e"

definition ifthenelse :: "(bool, 's) expr \<Rightarrow> 's prog \<Rightarrow> 's prog \<Rightarrow> 's prog" where
[expr_defs]: "ifthenelse b P Q = (if b\<^sup>< then P else Q)\<^sub>e"

definition assign :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) expr \<Rightarrow> 's prog"  where
[expr_defs]: "assign x e = ($x\<^sup>> = e\<^sup>< \<and> \<^bold>v\<^sup>> \<simeq>\<^bsub>\<guillemotleft>x\<guillemotright>\<^esub> \<^bold>v\<^sup><)\<^sub>e"

syntax 
  "_assign" :: "svid \<Rightarrow> logic \<Rightarrow> logic" ("_ ::= _" [86, 87] 87)
  "_ifthenelse" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("IF _ THEN _ ELSE _" [0, 0, 84] 84)

text \<open> The syntax translations insert the expression brackets, which means the expressions
  are lifted, without this being visible to the user. \<close>

translations 
  "_assign x e" == "CONST assign x (e)\<^sub>e"
  "_ifthenelse b P Q" == "CONST ifthenelse (b)\<^sub>e P Q"

lemma seq_assoc: "P ;; (Q ;; R) = (P ;; Q) ;; R"
  by expr_auto

lemma ifthenelse_seq_distr: "(IF B THEN P ELSE Q) ;; R = IF B THEN P ;; R ELSE Q ;; R"
  by expr_auto

lemma assign_twice:
  assumes "mwb_lens x"
  shows "x ::= e ;; x ::= f = x ::= f\<lbrakk>e/x\<rbrakk>"
  using assms
  apply expr_simp
  apply (metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)
  done

lemma assign_commute:
  assumes "mwb_lens x" "mwb_lens y" "x \<bowtie> y" "$y \<sharp> (e)\<^sub>e" "$x \<sharp> (f)\<^sub>e"
  shows "(x ::= e ;; y ::= f) = (y ::= f ;; x ::= e)"
  using assms
  apply expr_simp
  apply safe
  apply (metis lens_indep_def mwb_lens_weak weak_lens.put_get)+
  done

lemma assign_combine:
  assumes "mwb_lens x" "mwb_lens y" "x \<bowtie> y" "$x \<sharp> (f)\<^sub>e"
  shows "(x ::= e ;; y ::= f) = (x, y) ::= (e, f)"
  using assms
  apply expr_simp
  apply safe
  apply (simp_all add: lens_indep.lens_put_comm)
  apply (metis mwb_lens_weak weak_lens.put_get)
  done

text \<open> Below, we apply the assignment commutativity law in a small example: \<close>

declare [[literal_variables]]

lemma assign_commute_example: 
  "adam:name ::= ''Adam'' ;; bella:name ::= ''Bella'' = 
   bella:name ::= ''Bella'' ;; adam:name ::= ''Adam''"
proof (rule assign_commute)
  \<comment> \<open> We show the two variables satisfy the lens axioms \<close>
  show "mwb_lens (adam:name)\<^sub>v" by simp
  show "mwb_lens (bella:name)\<^sub>v" by simp

  \<comment> \<open> We show the two variables are independent \<close>
  show "(adam:name)\<^sub>v \<bowtie> (bella:name)\<^sub>v" by simp

  \<comment> \<open> We show that neither assigned expression depends on the opposite variable \<close>
  show "$bella:name \<sharp> (''Adam'')\<^sub>e" by unrest
  show "$adam:name \<sharp> (''Bella'')\<^sub>e" by unrest
qed
  
end