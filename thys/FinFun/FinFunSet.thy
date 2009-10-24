(*  Title:      FinFun/FinFunSet.thy
    Author:     Andreas Lochbihler
*)

header {*
  Sets modelled as FinFuns
*}

theory FinFunSet imports FinFun begin

text {* Instantiate FinFun predicates just like predicates as sets in Set.thy *}

types 'a set\<^isub>f = "'a \<Rightarrow>\<^isub>f bool"

instantiation "finfun" :: (type, ord) ord
begin

definition
  le_finfun_def [code del]: "f \<le> g \<longleftrightarrow> (\<forall>x. f\<^sub>f x \<le> g\<^sub>f x)"

definition
  less_fun_def: "(f\<Colon>'a \<Rightarrow>\<^isub>f 'b) < g \<longleftrightarrow> f \<le> g \<and> f \<noteq> g"

instance ..

lemma le_finfun_code [code]:
  "f \<le> g \<longleftrightarrow> finfun_All ((\<lambda>(x, y). x \<le> y) \<circ>\<^isub>f (f, g)\<^sup>f)"
by(simp add: le_finfun_def finfun_All_All o_def)

end

instantiation "finfun" :: (type, minus) minus
begin

definition
  finfun_diff_def: "A - B = split (op -) \<circ>\<^isub>f (A, B)\<^sup>f"

instance ..

end

instantiation "finfun" :: (type, uminus) uminus
begin

definition
  finfun_Compl_def: "- A = uminus \<circ>\<^isub>f A"

instance ..

end

text {*
  Replicate set operations for FinFuns
*}

definition finfun_empty :: "'a set\<^isub>f" ("{}\<^isub>f")
where "{}\<^isub>f \<equiv> (\<lambda>\<^isup>f False)"

definition finfun_insert :: "'a \<Rightarrow> 'a set\<^isub>f \<Rightarrow> 'a set\<^isub>f" ("insert\<^isub>f")
where "insert\<^isub>f a A = A(\<^sup>f a := True)"

definition finfun_mem :: "'a \<Rightarrow> 'a set\<^isub>f \<Rightarrow> bool" ("_/ \<in>\<^isub>f _" [50, 51] 50)
where "a \<in>\<^isub>f A = A\<^sub>f a"

definition finfun_UNIV :: "'a set\<^isub>f" 
where "finfun_UNIV = (\<lambda>\<^isup>f True)"

definition finfun_Un :: "'a set\<^isub>f \<Rightarrow> 'a set\<^isub>f \<Rightarrow> 'a set\<^isub>f" (infixl "\<union>\<^isub>f" 65)
where "A \<union>\<^isub>f B = split (op \<or>) \<circ>\<^isub>f (A, B)\<^sup>f"

definition finfun_Int :: "'a \<Rightarrow>\<^isub>f bool \<Rightarrow> 'a \<Rightarrow>\<^isub>f bool \<Rightarrow> 'a \<Rightarrow>\<^isub>f bool" (infixl "\<inter>\<^isub>f" 65)
where "A \<inter>\<^isub>f B = split (op \<and>) \<circ>\<^isub>f (A, B)\<^sup>f"

abbreviation finfun_subset_eq :: "'a set\<^isub>f \<Rightarrow> 'a set\<^isub>f \<Rightarrow> bool" where
  "finfun_subset_eq \<equiv> less_eq"

abbreviation
  finfun_subset :: "'a set\<^isub>f \<Rightarrow> 'a set\<^isub>f \<Rightarrow> bool" where
  "finfun_subset \<equiv> less"

notation (output)
  finfun_subset  ("op <\<^isub>f") and
  finfun_subset  ("(_/ <\<^isub>f _)" [50, 51] 50) and
  finfun_subset_eq  ("op <=\<^isub>f") and
  finfun_subset_eq  ("(_/ <=\<^isub>f _)" [50, 51] 50)

notation (xsymbols)
  finfun_subset  ("op \<subset>\<^isub>f") and
  finfun_subset  ("(_/ \<subset>\<^isub>f _)" [50, 51] 50) and
  finfun_subset_eq  ("op \<subseteq>\<^isub>f") and
  finfun_subset_eq  ("(_/ \<subseteq>\<^isub>f _)" [50, 51] 50)

notation (HTML output)
  finfun_subset  ("op \<subset>\<^isub>f") and
  finfun_subset  ("(_/ \<subset>\<^isub>f _)" [50, 51] 50) and
  finfun_subset_eq  ("op \<subseteq>\<^isub>f") and
  finfun_subset_eq  ("(_/ \<subseteq>\<^isub>f _)" [50, 51] 50)

lemma finfun_mem_empty [simp]: "a \<in>\<^isub>f {}\<^isub>f = False"
by(simp add: finfun_mem_def finfun_empty_def)

lemma finfun_subsetI [intro!]: "(!!x. x \<in>\<^isub>f A ==> x \<in>\<^isub>f B) ==> A \<subseteq>\<^isub>f B"
by(auto simp add: finfun_mem_def le_finfun_def le_bool_def)

lemma finfun_subsetD [elim]: "A \<subseteq>\<^isub>f B ==> c \<in>\<^isub>f A ==> c \<in>\<^isub>f B"
by(simp add: finfun_mem_def le_finfun_def le_bool_def)

lemma finfun_subset_refl [simp]: "A \<subseteq>\<^isub>f A"
  by fast

lemma finfun_set_ext: "(!!x. (x \<in>\<^isub>f A) = (x \<in>\<^isub>f B)) \<Longrightarrow> A = B"
by(simp add: expand_finfun_eq finfun_mem_def expand_fun_eq)

lemma finfun_subset_antisym [intro!]: "A \<subseteq>\<^isub>f B ==> B \<subseteq>\<^isub>f A ==> A = B"
  by (iprover intro: finfun_set_ext finfun_subsetD)

lemma finfun_Compl_iff [simp]: "(c \<in>\<^isub>f -A) = (\<not> c \<in>\<^isub>f A)"
by (simp add: finfun_mem_def finfun_Compl_def bool_Compl_def)

lemma finfun_Un_iff [simp]: "(c \<in>\<^isub>f A \<union>\<^isub>f B) = (c \<in>\<^isub>f A | c \<in>\<^isub>f B)"
by (simp add: finfun_Un_def finfun_mem_def)

lemma finfun_Int_iff [simp]: "(c \<in>\<^isub>f A \<inter>\<^isub>f B) = (c \<in>\<^isub>f A & c \<in>\<^isub>f B)"
by(simp add: finfun_Int_def finfun_mem_def)

lemma finfun_Diff_iff [simp]: "(c \<in>\<^isub>f A - B) = (c \<in>\<^isub>f A & \<not> c \<in>\<^isub>f B)"
by (simp add: finfun_mem_def finfun_diff_def bool_diff_def)

lemma finfun_insert_iff [simp]: "(a \<in>\<^isub>f insert\<^isub>f b A) = (a = b | a \<in>\<^isub>f A)"
by(simp add: finfun_insert_def finfun_mem_def finfun_upd_apply)

text {* A tail-recursive function that never terminates in the code generator *}

definition loop_counting :: "nat \<Rightarrow> (unit \<Rightarrow> 'a) \<Rightarrow> 'a"
where [simp, code del]: "loop_counting n f = f ()"

lemma loop_counting_code [code]: "loop_counting n = loop_counting (Suc n)"
by(simp add: expand_fun_eq)

definition loop :: "(unit \<Rightarrow> 'a) \<Rightarrow> 'a"
where [simp, code del]: "loop f = f ()"

lemma loop_code [code]: "loop = loop_counting 0"
by(simp add: expand_fun_eq)

lemma mem_finfun_apply_conv: "x \<in> f\<^sub>f \<longleftrightarrow> f\<^sub>f x"
by(simp add: mem_def)

text {* Bounded quantification.

  Warning: @{text "finfun_Ball"} and @{text "finfun_Ex"} may fail to terminate, they should not be used for quickcheck
*}

definition finfun_Ball_except :: "'a list \<Rightarrow> 'a set\<^isub>f \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where [code del]: "finfun_Ball_except xs A P = (\<forall>a\<in>A\<^sub>f. a \<in> set xs \<or> P a)"

lemma finfun_Ball_except_const:
  "finfun_Ball_except xs (\<lambda>\<^isup>f b) P \<longleftrightarrow> \<not> b \<or> set xs = UNIV \<or> loop (\<lambda>u. finfun_Ball_except xs (\<lambda>\<^isup>f b) P)"
by(auto simp add: finfun_Ball_except_def mem_finfun_apply_conv)

lemma finfun_Ball_except_const_finfun_UNIV_code [code]:
  "finfun_Ball_except xs (\<lambda>\<^isup>f b) P \<longleftrightarrow> \<not> b \<or> is_list_UNIV xs \<or> loop (\<lambda>u. finfun_Ball_except xs (\<lambda>\<^isup>f b) P)"
by(auto simp add: finfun_Ball_except_def is_list_UNIV_iff mem_finfun_apply_conv)

lemma finfun_Ball_except_update: 
  "finfun_Ball_except xs (A(\<^sup>f a := b)) P = ((a \<in> set xs \<or> (b \<longrightarrow> P a)) \<and> finfun_Ball_except (a # xs) A P)"
by(fastsimp simp add: finfun_Ball_except_def mem_finfun_apply_conv finfun_upd_apply dest: bspec split: split_if_asm)

lemma finfun_Ball_except_update_code [code]:
  fixes a :: "'a :: card_UNIV"
  shows "finfun_Ball_except xs (finfun_update_code f a b) P = ((a \<in> set xs \<or> (b \<longrightarrow> P a)) \<and> finfun_Ball_except (a # xs) f P)"
by(simp add: finfun_Ball_except_update)

definition finfun_Ball :: "'a set\<^isub>f \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where [code del]: "finfun_Ball A P = Ball (A\<^sub>f) P"

lemma finfun_Ball_code [code]: "finfun_Ball = finfun_Ball_except []"
by(auto intro!: ext simp add: finfun_Ball_except_def finfun_Ball_def)


definition finfun_Bex_except :: "'a list \<Rightarrow> 'a set\<^isub>f \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where [code del]: "finfun_Bex_except xs A P = (\<exists>a\<in>A\<^sub>f. a \<notin> set xs \<and> P a)"

lemma finfun_Bex_except_const: "finfun_Bex_except xs (\<lambda>\<^isup>f b) P \<longleftrightarrow> b \<and> set xs \<noteq> UNIV \<and> loop (\<lambda>u. finfun_Bex_except xs (\<lambda>\<^isup>f b) P)"
by(auto simp add: finfun_Bex_except_def mem_finfun_apply_conv)

lemma finfun_Bex_except_const_finfun_UNIV_code [code]:
  "finfun_Bex_except xs (\<lambda>\<^isup>f b) P \<longleftrightarrow> b \<and> \<not> is_list_UNIV xs \<and> loop (\<lambda>u. finfun_Bex_except xs (\<lambda>\<^isup>f b) P)"
by(auto simp add: finfun_Bex_except_def is_list_UNIV_iff mem_finfun_apply_conv)

lemma finfun_Bex_except_update: 
  "finfun_Bex_except xs (A(\<^sup>f a := b)) P \<longleftrightarrow> (a \<notin> set xs \<and> b \<and> P a) \<or> finfun_Bex_except (a # xs) A P"
by(fastsimp simp add: finfun_Bex_except_def mem_finfun_apply_conv finfun_upd_apply dest: bspec split: split_if_asm)

lemma finfun_Bex_except_update_code [code]:
  fixes a :: "'a :: card_UNIV"
  shows "finfun_Bex_except xs (finfun_update_code f a b) P \<longleftrightarrow> ((a \<notin> set xs \<and> b \<and> P a) \<or> finfun_Bex_except (a # xs) f P)"
by(simp add: finfun_Bex_except_update)

definition finfun_Bex :: "'a set\<^isub>f \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where [code del]: "finfun_Bex A P = Bex (A\<^sub>f) P"

lemma finfun_Bex_code [code]: "finfun_Bex = finfun_Bex_except []"
by(auto intro!: ext simp add: finfun_Bex_except_def finfun_Bex_def)

text {* Automatically replace set operations by finfun set operations where possible *}

lemma iso_finfun_mem_mem [code_inline]: "x \<in> A\<^sub>f \<longleftrightarrow> x \<in>\<^isub>f A"
by(auto simp add: mem_def finfun_mem_def)

declare iso_finfun_mem_mem [simp]

lemma iso_finfun_subset_subset [code_inline]:
  "A\<^sub>f \<subseteq> B\<^sub>f \<longleftrightarrow> A \<subseteq>\<^isub>f B"
by(auto)

lemma iso_finfun_eq [code_inline]:
  fixes A :: "'a \<Rightarrow>\<^isub>f bool"
  shows "A\<^sub>f = B\<^sub>f \<longleftrightarrow> A = B"
by(simp add: expand_finfun_eq)

lemma iso_finfun_Un_Un [code_inline]:
  "A\<^sub>f \<union> B\<^sub>f = (A \<union>\<^isub>f B)\<^sub>f"
by(auto)

lemma iso_finfun_Int_Int [code_inline]:
  "A\<^sub>f \<inter> B\<^sub>f = (A \<inter>\<^isub>f B)\<^sub>f"
by(auto)

lemma iso_finfun_empty_conv [code_inline]:
  "{} = {}\<^isub>f\<^sub>f"
by(auto)

lemma iso_finfun_insert_insert [code_inline]:
  "insert a A\<^sub>f = (insert\<^isub>f a A)\<^sub>f"
by(auto)

lemma iso_finfun_Compl_Compl [code_inline]:
  fixes A :: "'a set\<^isub>f"
  shows "- A\<^sub>f = (- A)\<^sub>f"
by(auto)

lemma iso_finfun_diff_diff [code_inline]:
  fixes A :: "'a set\<^isub>f"
  shows "A\<^sub>f - B\<^sub>f = (A - B)\<^sub>f"
by(auto)

text {*
  Do not declare the following two theorems as @{text "[code_inline]"}, because this causes quickcheck to loop frequently when bounded quantification is used.
  For code generation, the same problems occur, but then, no randomly generated FinFun is usually around.
*}

lemma iso_finfun_Ball_Ball:
  "Ball (A\<^sub>f) P \<longleftrightarrow> finfun_Ball A P"
by(simp add: finfun_Ball_def)

lemma iso_finfun_Bex_Bex:
  "Bex (A\<^sub>f) P \<longleftrightarrow> finfun_Bex A P"
by(simp add: finfun_Bex_def)

declare iso_finfun_mem_mem [simp del]

end