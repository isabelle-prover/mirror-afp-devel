theory Vectors

imports 
  Main 
  "~~/src/HOL/Number_Theory/Binomial"
  "~~/src/HOL/Library/FuncSet"
begin

definition vector::"['a list, nat] \<Rightarrow> bool"
  where "vector l n = 
        (length l=n)"

definition Avector::"['a list, 'a set, nat] \<Rightarrow> bool"
  where "Avector l A n = 
        ((length l = n) \<and> (\<forall> i. i<n \<longrightarrow> l ! i \<in> A))"

definition vectors::"[nat] \<Rightarrow> 'a list set"
  where "vectors n = 
        {l. length l=n}"

definition Avectors::"['a set, nat] \<Rightarrow> 'a list set"
  where "Avectors A n = 
        {l. ((length l = n) \<and> (\<forall> i. i<n \<longrightarrow> l ! i \<in> A))}"

lemma Avector_lists: "Avector l A n \<longleftrightarrow> length l = n \<and> l \<in> lists A"
  by (auto simp: Avector_def) (metis in_set_conv_nth)

lemma Avector_0 [simp]: "Avector l A 0 \<longleftrightarrow> l=[]"
  by (auto simp: Avector_def)

lemma Avector_Suc [simp]: "Avector l A (Suc n) \<longleftrightarrow> (\<exists>x xs. l = x#xs \<and> x \<in> A \<and> Avector xs A n)"
  by (cases l) (auto simp add: Avector_lists)

lemma Avector_cons:
  assumes "Avector l A n" "a\<in>A"
  shows "Avector (a#l) A (n + 1)"
  by (simp add: assms)

(*with dependent types this would be Vector A n \<Rightarrow> ({..<n} \<Rightarrow> A)*)
definition vec_to_func ::"'a list \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "vec_to_func l = (\<lambda>i. if (i < length l) then l ! i else undefined)"

definition func_to_vec ::"nat \<Rightarrow>(nat \<Rightarrow> 'a) \<Rightarrow> 'a list" where
  "func_to_vec n f = [f i. i \<leftarrow> [0..<n]]"

abbreviation inverses :: "'a set \<Rightarrow>'b set \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "inverses A B f g \<equiv> (f\<in>A\<rightarrow>B)\<and>(g\<in>B\<rightarrow>A)\<and> (\<forall> a\<in>A. g (f a) = a) \<and> (\<forall>b\<in>B. f (g b) = b)"


lemma func_vec_inverses: 
  "inverses (Avectors A n) ({..<n}\<rightarrow>\<^sub>E A) vec_to_func (func_to_vec n)"
proof -
  let ?f="vec_to_func"
  let ?g="func_to_vec n"
  from assms have 1: "vec_to_func \<in> Avectors A n \<rightarrow> ({..<n}\<rightarrow>\<^sub>EA)"
    apply (unfold Avectors_def)
    apply auto
    apply (unfold vec_to_func_def)
    by (auto split: split_if_asm)
  from assms have 2: "func_to_vec n \<in> ({..<n}\<rightarrow>\<^sub>EA) \<rightarrow> Avectors A n"
    apply (unfold Avectors_def)
    apply (intro Pi_I)
    apply (unfold func_to_vec_def)
    by (auto split: split_if_asm)
  from assms have 3: "\<And>a. a\<in>(Avectors A n) \<Longrightarrow> ?g (?f a) = a"
    apply (unfold Avectors_def func_to_vec_def vec_to_func_def)
    apply auto
    by (subst list_eq_iff_nth_eq, auto)
  from assms have 4: "\<And>b. b\<in>({..<n}\<rightarrow>\<^sub>E A) \<Longrightarrow> ?f (?g b) = b"
    apply (unfold Avectors_def func_to_vec_def vec_to_func_def PiE_def)
    by (auto intro!: extensionalityI simp add: extensional_def)
  from 1 2 3 4 show ?thesis by auto
qed

 (*"\<Sum>x<-xs. f x"*)

lemma bijection_card_eq:
  fixes A B
  assumes A_fin: "finite B" and 
    inv: "inverses A B f g"
  shows "finite A \<and> card A = card B"
proof - 
  from assms have bij: "bij_betw f A B" 
    apply (unfold bij_betw_def inj_on_def image_def, auto)
    apply metis
    by (metis funcset_mem)
  from A_fin bij have fin: "finite A" 
    by (metis bij_betw_finite)
(*apply (unfold bij_betw_def, auto)
by (metis finite_imageD)*)
  from assms bij have card_eq: "card A = card B"
    by (metis bij_betw_same_card)
  from fin card_eq show ?thesis by auto
qed

lemma bijection_proof:
  fixes A B n
  assumes
    inv: "inverses A B f g"
    and B_card: "finite B \<and> card B = n"
  shows "finite A\<and> card A = n"
proof -
  from assms show ?thesis
    apply (insert assms)
    by (metis bijection_card_eq)
qed

(*
definition combinations::"nat \<Rightarrow> nat \<Rightarrow> bool list set"
  where "combinations m n = {l::bool list. vector l n \<and> card {i. l ! i} = m}"
*)
(*
definition combinations::"nat \<Rightarrow> nat \<Rightarrow> nat list set"
  where "combinations n m  = {l::nat list. (Avector l {0,1} n \<and> (\<Sum>x \<leftarrow> l. x) = m)}"
*)

lemma Avectors_card: 
  assumes A_fin: "finite A"
  shows "finite (Avectors A n) \<and> card (Avectors A n) = (card A) ^ n"
proof -
  from A_fin have fin: "finite ({..<n} \<rightarrow>\<^sub>E A)"
    by (intro finite_PiE, auto)
  from A_fin have card: "card ({..<n} \<rightarrow>\<^sub>E A) = (card A) ^ n"
    apply (subst card_PiE, auto)
    by (metis card_lessThan finite_lessThan setprod_constant)
  from fin card show "finite (Avectors A n)\<and> card (Avectors A n) = (card A) ^ n"
    apply (insert fin card func_vec_inverses)
    apply (intro bijection_proof(1)[where ?A="Avectors A n" and ?B="{..<n} \<rightarrow>\<^sub>E A"
      and ?f="vec_to_func" and ?g="func_to_vec n"])
    apply (simp add: func_vec_inverses)
    by blast
qed
  

end
