(*   Title:      Formal Proof of Dilworth's Theorem
     Author:  Vivek Soorya Maadoori, Syed Mohammad Meesum, Shiv Pillai, T.V.H. Prathamesh, Aditya Swami,  2025
     Maintainer:  Vivek Soorya Maadoori, Syed Mohammad Meesum, Shiv Pillai, T.V.H. Prathamesh, Aditya Swami
 *)



theory Dilworth
imports Main HOL.Complete_Partial_Order HOL.Relation HOL.Order_Relation 
        "Min_Max_Least_Greatest.Min_Max_Least_Greatest_Set"
begin


text \<open>Note: The Dilworth's theorem for chain cover is labelled Dilworth and the 
extension to chain decomposition is labelled Dilworth\_Decomposition.\<close>

context order
begin

section "Definitions"

definition chain_on :: "_ set  \<Rightarrow> _ set \<Rightarrow> bool" where
"chain_on A S \<longleftrightarrow> ((A \<subseteq> S) \<and> (Complete_Partial_Order.chain (\<le>) A))"

definition antichain :: "  _ set \<Rightarrow> bool" where
"antichain S \<longleftrightarrow> (\<forall>x \<in> S. \<forall>y \<in> S. ( x \<le> y \<or> y \<le> x) \<longrightarrow> x = y)"

definition antichain_on :: "_ set  \<Rightarrow> _ set \<Rightarrow> bool" where
"(antichain_on A S) \<longleftrightarrow> 
  (partial_order_on A (relation_of (\<le>) A)) \<and> (S \<subseteq> A) \<and> (antichain  S)"

definition largest_antichain_on:: "_ set  \<Rightarrow> _ set \<Rightarrow> bool" where
"largest_antichain_on P lac \<longleftrightarrow> 
  (antichain_on P lac \<and> (\<forall> ac. antichain_on P  ac \<longrightarrow> card ac \<le> card lac))"

definition chain_cover_on:: "_ set  \<Rightarrow> _ set set \<Rightarrow> bool" where
"chain_cover_on S cv \<longleftrightarrow> (\<Union> cv = S) \<and> (\<forall> x \<in> cv . chain_on x S)"

definition antichain_cover_on:: "_ set \<Rightarrow> _ set set \<Rightarrow> bool" where
"antichain_cover_on S cv \<longleftrightarrow> (\<Union> cv = S) \<and> (\<forall> x \<in> cv . antichain_on S  x)"

definition smallest_chain_cover_on:: "_ set  \<Rightarrow> _ set set \<Rightarrow> bool" where
"smallest_chain_cover_on S cv \<equiv> 
  (chain_cover_on S cv \<and> 
  (\<forall> cv2. (chain_cover_on S cv2 \<and> card cv2 \<le> card cv) \<longrightarrow> card cv = card cv2))"

definition chain_decomposition where  
"chain_decomposition S cd \<equiv> ((chain_cover_on S cd) \<and> 
                             (\<forall> x \<in> cd. \<forall> y \<in> cd. x \<noteq> y \<longrightarrow> (x \<inter> y = {})))"

definition smallest_chain_decomposition:: "_ set  \<Rightarrow> _ set set \<Rightarrow> bool" where
"smallest_chain_decomposition S cd 
  \<equiv> (chain_decomposition S cd 
      \<and> (\<forall> cd2. (chain_decomposition S cd2 \<and> card cd2 \<le> card cd) 
                                          \<longrightarrow> card cd = card cd2))"

section "Preliminary Lemmas"

text \<open> The following lemma shows that given a chain and an antichain, if the cardinality of their
 intersection is equal to 0, then their intersection is empty..\<close>


lemma inter_nInf: 
  assumes a1: "Complete_Partial_Order.chain (\<subseteq>)  X" 
      and a2: "antichain Y"
  and asmInf: "card (X \<inter> Y) = 0"
        shows "X \<inter> Y = {}"
proof (rule ccontr)
  assume "X \<inter> Y \<noteq> {}"
  then obtain a b where 1:"a \<in> (X \<inter> Y)" "b \<in> (X \<inter> Y)" using asmInf by blast
  then have in_chain: "a \<in> X \<and> b \<in> X" using 1 by simp
  then have 3: "(a \<le> b) \<or> (b \<le> a)" using  a1 
    by (simp add: chain_def) 
  have in_antichain: "a \<in> Y \<and> b \<in> Y" using 1 by blast
  then have "a = b" using antichain_def a2 3 
    by (metis order_class.antichain_def)
  then have "\<forall> a \<in> (X \<inter> Y). \<forall> b \<in> (X \<inter> Y). a = b" 
    using 1 a1 a2 order_class.antichain_def
    by (smt (verit, best) IntE chain_def)
  then have "card (X \<inter> Y) = 1" using 1 a1 a2 card_def
    by (smt (verit, best) all_not_in_conv asmInf card_0_eq card_le_Suc0_iff_eq 
        finite_if_finite_subsets_card_bdd subset_eq subset_iff)
  then show False using asmInf by presburger
qed

text \<open> The following lemma shows that given a chain X and an antichain Y that both are subsets of S, their intersection
is either empty or has cardinality one..\<close>

lemma chain_antichain_inter: 
  assumes a1: "Complete_Partial_Order.chain (\<subseteq>)  X"  
      and a2: "antichain Y"
      and a3: "X \<subseteq> S \<and> Y \<subseteq> S"
        shows "(card (X \<inter> Y) = 1) \<or> ((X \<inter> Y) = {})"
proof (cases "card (X \<inter> Y) \<ge> 1")
  case True
  then obtain a b where 1:"a \<in> (X \<inter> Y)" "b \<in> (X \<inter> Y)"
    by (metis card_1_singletonE insert_subset obtain_subset_with_card_n)
  then have "a \<in> X \<and> b \<in> X" using 1 by blast
  then have 3: "(a \<le> b) \<or> (b \<le> a)" using Complete_Partial_Order.chain_def a1 
    by (smt (verit, best)) 
  have "a \<in> Y \<and> b \<in> Y" using 1 by blast
  then have "a = b" using a2 order_class.antichain_def 3 
    by (metis)
  then have "\<forall> a \<in> (X \<inter> Y). \<forall> b \<in> (X \<inter> Y). a = b" 
    using 1 a1 a2 order_class.antichain_def
    by (smt (verit, best) Int_iff chainD)
  then have "card (X \<inter> Y) = 1" using 1 a1 a2
    by (metis One_nat_def True card.infinite card_le_Suc0_iff_eq 
              order_class.order_antisym zero_less_one_class.zero_le_one)
  then show ?thesis by presburger
next
  case False
  then have "card (X \<inter> Y) < 1" by linarith
  then have "card (X \<inter> Y) = 0" by blast
  then have "X \<inter> Y = {}" using assms inter_nInf by blast
  then show ?thesis by force
qed

text \<open>Following lemmas show that given a finite set S, there exists a chain decomposition of S.\<close>

lemma po_restr: assumes "partial_order_on B r" 
                    and "A \<subseteq> B" 
                  shows "partial_order_on A (r \<inter> (A \<times> A))"
  using assms 
  unfolding partial_order_on_def preorder_on_def antisym_def refl_on_def trans_def
  by (metis (no_types, lifting) IntD1 IntD2 IntI Int_lower2 inf.orderE mem_Sigma_iff)


lemma eq_restr: "(Restr (relation_of (\<le>) (insert a A)) A) = (relation_of (\<le>) A)" 
  (is "?P = ?Q")
proof
  show "?P \<subseteq> ?Q"
  proof
    fix z
    assume "z \<in> ?P"
    then obtain x y where tuple: "(x, y) = z" using relation_of_def by blast
    then have 1: "(x, y) \<in> ((relation_of (\<le>) (insert a A)) \<inter> (A \<times> A))" 
      using relation_of_def
      using \<open>z \<in> Restr (relation_of (\<le>) (insert a A)) A\<close> by blast
    then have 2: "(x, y) \<in> (relation_of (\<le>) (insert a A))" by simp
    then have 3: "(x, y) \<in> (A \<times> A)" using 1 by simp
    then have "(x, y) \<in> (A \<times> A) \<and> (x \<le> y)" using relation_of_def 2
      by (metis (no_types, lifting) case_prodD mem_Collect_eq)
    then have "(x, y) \<in> (relation_of (\<le>) A)" using relation_of_def by blast
    then show "z \<in> ?Q" using tuple by fast
  qed
next
  show "?Q \<subseteq> ?P"
  proof
    fix z
    assume asm1: "z \<in> ?Q"
    then obtain x y where tuple: "(x, y) = z" by (metis prod.collapse)
    then have 0: "(x, y) \<in> (A \<times> A) \<and> (x \<le> y)" using asm1 relation_of_def
      by (metis (mono_tags, lifting) case_prod_conv mem_Collect_eq)
    then have 1: "(x, y) \<in> (A \<times> A)" by fast
    have rel: "x \<le> y" using 0 by blast
    have "(A \<times> A) \<subseteq> ((insert a A) \<times> (insert a A))" by blast
    then have "(x, y) \<in> ((insert a A) \<times> (insert a A))" using 1 by blast
    then have "(x, y) \<in> (relation_of (\<le>) (insert a A))" 
      using rel relation_of_def by blast
    then have "(x, y) \<in> ((relation_of (\<le>) (insert a A)) \<inter> (A \<times> A))" using 1 by fast
    then show "z \<in> ?P" using tuple by fast
  qed
qed

lemma part_ord:"partial_order_on S (relation_of (\<le>) S)" 
  by (smt (verit, ccfv_SIG) local.dual_order.eq_iff local.dual_order.trans 
      partial_order_on_relation_ofI)

text \<open>The following lemma shows that a chain decomposition exists for any finite set S.\<close>

lemma exists_cd: assumes "finite S"
                   shows "\<exists> cd. chain_decomposition S cd" 
   using assms
proof(induction rule: finite.induct)
  case emptyI
  then show ?case using assms unfolding chain_decomposition_def chain_cover_on_def
    by (metis Sup_empty empty_iff)
next
  case (insertI A a)
  show ?case using assms
  proof (cases "a \<in> A")
    case True
    then have 1: "(insert a A) = A" by fast
    then have "\<exists> X. chain_decomposition A X" using insertI by simp
    then show ?thesis using 1 by auto
  next
    case False
    have subset_a: "{a} \<subseteq> (insert a A)" by simp
    have chain_a: "Complete_Partial_Order.chain (\<le>) {a}" 
      using chain_singleton chain_def by auto
    have subset_A: "A \<subseteq> (insert a A)" by blast
    have partial_a: "partial_order_on A ((relation_of (\<le>) (insert a A)) \<inter> (A \<times> A))"
      using po_restr insertI subset_A part_ord by blast
    then have chain_on_A: "chain_on  {a} (insert a A)" 
      unfolding order_class.chain_on_def using chain_a partial_a 
                insertI.prems chain_on_def by simp 
    then  obtain X where chain_set: "chain_decomposition  A X" 
      using insertI partial_a eq_restr 
      by auto 
    have chains_X: "\<forall> x \<in> (insert {a} X). chain_on x (insert a A)" 
      using subset_A chain_set chain_on_def 
            chain_decomposition_def chain_cover_on_def chain_on_A
      by auto
    have subsets_X: "\<forall> x \<in> (insert {a} X). x \<subseteq> (insert a A)" 
      using chain_set chain_decomposition_def subset_a chain_cover_on_def
      by auto
    have null_inter_X: "\<forall> x \<in> X. \<forall> y \<in> X. x \<noteq> y \<longrightarrow> x \<inter> y = {}"
      using chain_set chain_decomposition_def 
      by (simp add: order_class.chain_decomposition_def)
    have "{a} \<notin> X" using False chain_set chain_decomposition_def chain_cover_on_def
      by (metis UnionI insertCI)
    then have null_inter_a: "\<forall> x \<in> X. {a} \<inter> x = {}"
      using False chain_set order_class.chain_decomposition_def 
      using chain_decomposition_def chain_cover_on_def by auto
    then have null_inter: "\<forall> x \<in> (insert {a} X). \<forall> y \<in> (insert {a} X). x \<noteq> y \<longrightarrow> x \<inter> y = {}" 
      using null_inter_X by simp
    have union: "\<Union> (insert {a} X) = (insert a A)" using chain_set
      by (simp add: chain_decomposition_def chain_cover_on_def)
    have "chain_decomposition (insert a A)  (insert {a} X)"
      using subsets_X chains_X union null_inter unfolding chain_decomposition_def 
            chain_cover_on_def  
      by simp
    then show ?thesis by blast
  qed
qed

text \<open>The following lemma shows that the chain decomposition of a set is a chain cover.\<close>

lemma cd_cv: 
  assumes "chain_decomposition P cd"
  shows "chain_cover_on P cd"
  using assms unfolding chain_decomposition_def by argo

text \<open>The following lemma shows that for any finite partially ordered set, there exists a chain cover on that set.\<close>

lemma exists_chain_cover: assumes "finite P"
                   shows "\<exists> cv. chain_cover_on P  cv"
proof-
  show ?thesis using assms exists_cd cd_cv by blast
qed

lemma finite_cv_set: assumes "finite P"
                         and "S = {x. chain_cover_on P x}"
                       shows "finite S"
proof-
  have 1: "\<forall> cv. chain_cover_on P cv \<longrightarrow> (\<forall> c \<in> cv. finite c)" 
    unfolding chain_cover_on_def chain_on_def chain_def
    using assms(1) rev_finite_subset by auto 
  have 2: "\<forall> cv. chain_cover_on P cv \<longrightarrow> finite cv" 
    unfolding chain_cover_on_def
    using assms(1) finite_UnionD by auto
  have "\<forall> cv. chain_cover_on P cv \<longrightarrow> (\<forall> c \<in> cv. c \<subseteq> P)" 
    unfolding chain_cover_on_def by blast
  then have "\<forall> cv. chain_cover_on P cv \<longrightarrow> cv \<subseteq> Fpow P" using Fpow_def 1 by fast
  then have "\<forall> cv. chain_cover_on P cv \<longrightarrow> cv \<in> Fpow (Fpow P)" 
    using Fpow_def 2 by fast
  then have "S \<subseteq> Fpow (Fpow P)" using assms(2) by blast
  then show ?thesis 
    using assms(1) by (meson Fpow_subset_Pow finite_Pow_iff finite_subset)
qed


text \<open>The following lemma shows that for every element of an antichain in a set, there exists a chain in the 
chain cover of that set, such that the element of the antichain belongs to the chain.\<close>

lemma elem_ac_in_c: assumes a1: "antichain_on P  ac" 
                        and "chain_cover_on P  cv"
                      shows "\<forall> a \<in> ac. \<exists> c \<in> cv. a \<in> c"
proof-
  have "\<Union> cv = P" using assms(2) chain_cover_on_def by simp
  then have "ac \<subseteq> \<Union> cv" using a1 antichain_on_def by simp
  then show "\<forall> a \<in> ac. \<exists> c \<in> cv. a \<in> c" by blast
qed

text \<open> For a function f that maps every element of an antichain to
some chain it belongs to in a chain cover, we show that, the co-domain of f is a subset of 
the chain cover.\<close>

lemma f_image: fixes f :: "_ \<Rightarrow> _ set"
             assumes a1: "(antichain_on P  ac)"
                 and a2: "(chain_cover_on P  cv)"
                 and a3: "\<forall>a \<in> ac. \<exists> c \<in> cv. a \<in> c \<and> f a = c"
               shows "(f ` ac) \<subseteq> cv"
proof
  have 1: "\<forall>a \<in> ac. \<exists> c \<in> cv. a \<in> c" using elem_ac_in_c a1 a2 by presburger
  fix y
  assume "y \<in> (f ` ac)"
  then obtain x where "f x = y" " x \<in> ac" using a1 a2 by auto
  then have "x \<in> y" using a3 by blast
  then show "y \<in> cv" using a3 using \<open>f x = y\<close> \<open>x \<in> ac\<close> by blast
qed

section "Size of an antichain is less than or equal to the 
size of a chain cover"

text \<open>The following lemma shows that given an antichain ac and chain cover cv on a finite set, the 
cardinality of ac will be less than or equal to the cardinality of cv.\<close>

lemma antichain_card_leq: 
           assumes "(antichain_on P ac)"
               and "(chain_cover_on P  cv)"
               and "finite P"
             shows "card ac \<le> card cv"
proof (rule ccontr)
  assume a_contr: "\<not> card ac \<le> card cv"
  then have 1: "card cv < card ac" by simp
  have finite_cv: "finite cv" using assms(2,3) chain_cover_on_def
    by (simp add: finite_UnionD)
  have 2: "\<forall> a \<in> ac. \<exists> c \<in> cv. a \<in> c" using assms(1,2) elem_ac_in_c by simp
  then obtain f where f_def: "\<forall>a \<in> ac. \<exists> c \<in> cv. a \<in> c \<and> f a = c" by metis
  then have "(f ` ac) \<subseteq> cv" using f_image assms by blast
  then have 3: "card (f ` ac) \<le> card cv" using f_def finite_cv card_mono by metis
  then have "card (f ` ac) < card ac" using 1 by auto
  then have "\<not> inj_on f ac" using pigeonhole by blast
  then obtain a b where p1: "f a = f b" "a \<noteq> b" "a \<in> ac" "b \<in> ac" 
    using inj_def f_def by (meson inj_on_def)
  then have antichain_elem: "a \<in> ac \<and> b \<in> ac" using f_def by blast
  then have "\<exists> c \<in> cv. f a = c \<and> f b = c" using f_def 2 1 \<open>f ` ac \<subseteq> cv\<close> p1(1) by auto
  then have chain_elem: "\<exists> c \<in> cv. a \<in> c \<and> b \<in> c" 
    using f_def p1(1) p1(3) p1(4) by blast
  then have "a \<le> b \<or> b \<le> a" using chain_elem chain_cover_on_def chain_on_def 
    by (metis assms(2) chainD) 
  then have "a = b" 
    using antichain_elem assms(1) antichain_on_def antichain_def by auto
  then show False using p1(2) by blast
qed

section "Existence of a chain cover whose cardinality is the cardinality of the 
largest antichain"

subsection "Preliminary lemmas"

text \<open>The following lemma shows that the maximal set is an antichain.\<close>

lemma maxset_ac: "antichain ({x . is_maximal_in_set P x})" 
  using antichain_def local.is_maximal_in_set_iff by auto

text \<open> The following lemma shows that the minimal set is an antichain.\<close>

lemma minset_ac: "antichain ({x . is_minimal_in_set P x})" 
  using antichain_def is_minimal_in_set_iff by force


text \<open> The following lemma shows that the null set is both an antichain and a chain cover.\<close>

lemma antichain_null: "antichain {}"
proof-
  show ?thesis using antichain_def by simp
qed

lemma chain_cover_null: assumes "P = {}" shows "chain_cover_on P {}"
proof-
  show ?thesis using chain_cover_on_def
    by (simp add: assms)
qed

text \<open> The following lemma shows that for any arbitrary x that does not belong to the largest antichain of
 a set, there exists an element y in the antichain such that x is related to y or y is
 related to x.\<close>

lemma x_not_in_ac_rel: assumes "largest_antichain_on P  ac"
                           and "x \<in> P" 
                           and "x \<notin> ac"
                           and "finite P"
                         shows "\<exists> y \<in> ac. (x \<le> y) \<or> (y \<le> x)"
proof (rule ccontr)
  assume "\<not> (\<exists>y\<in>ac. x \<le> y \<or> y \<le> x)"
  then have 1: "\<forall> y \<in> ac. (\<not>(x \<le> y) \<and> \<not>(y \<le> x))" by simp
  then have 2: "\<forall> y \<in> ac. x \<noteq> y" by auto
  then obtain S where S_def: "S = {x} \<union> ac" by blast
  then have S_fin: "finite S" 
    using assms(4) assms(1) assms(2) largest_antichain_on_def antichain_on_def
    by (meson Un_least bot.extremum insert_subset rev_finite_subset)
  have S_on_P: "antichain_on P  S" 
    using S_def largest_antichain_on_def antichain_on_def assms(1,2) 1 2 antichain_def 
    by auto
  then have "ac \<subset> S" using S_def assms(3) by auto
  then have "card ac < card S" using psubset_card_mono S_fin by blast
  then show False using assms(1) largest_antichain_on_def S_on_P by fastforce
qed


text \<open>The following lemma shows that for any subset Q of the partially ordered P, if the minimal set of P is a subset 
of Q, then it is a subset of the minimal set of Q as well.\<close>

lemma minset_subset_minset:
  assumes "finite P"
      and "Q \<subseteq> P"
      and "\<forall> x. (is_minimal_in_set P x \<longrightarrow> x \<in> Q)"
    shows "{x . is_minimal_in_set P x} \<subseteq> {x. is_minimal_in_set Q x}" 
proof
  fix x
  assume asm1: "x \<in> {z. is_minimal_in_set P z}"
  have 1: "x \<in> Q" using asm1 assms(3)  
    by blast 
  have partial_Q: "partial_order_on Q (relation_of (\<le>) Q)" 
    using assms(1) assms(3) partial_order_on_def
    by (simp add: partial_order_on_relation_ofI)
  have "\<forall> q \<in> Q. q \<in> P" using assms(2) by blast
  then have "is_minimal_in_set Q x" using is_minimal_in_set_iff 1 partial_Q 
    using asm1 by force
  then show "x \<in> {z. is_minimal_in_set Q z}" by blast
qed

text \<open> The following lemma show that if P is not empty, 
the minimal set of P is not empty.\<close>

lemma non_empty_minset: assumes "finite P"
                            and "P \<noteq> {}"
                          shows "{x . is_minimal_in_set P x} \<noteq> {}"
  by (simp add: assms ex_minimal_in_set)


text \<open> The following lemma shows that for all elements m of the minimal set, there exists a 
chain c in the chain cover such that m belongs to c.\<close>

lemma elem_minset_in_chain: assumes "finite P"
                                and "chain_cover_on P cv"
                              shows "is_minimal_in_set P a \<longrightarrow> (\<exists> c \<in> cv. a \<in> c)" 
  using assms(2) chain_cover_on_def is_minimal_in_set_iff by auto


text \<open> The following lemma shows  that for all elements m of the maximal set, there exists a chain c 
in the chain cover such that m belongs to c.\<close>

lemma elem_maxset_in_chain: assumes "finite P"
                                and "chain_cover_on P  cv"
                              shows "is_maximal_in_set P a \<longrightarrow> (\<exists> c \<in> cv. a \<in> c)" 
  using chain_cover_on_def assms is_maximal_in_set_iff by auto


text \<open>The following lemma shows that for a given chain cover and antichain on P, 
if the cardinality of the chain cover is equal to the cardinality of the antichain 
then for all chains c of the chain cover, there exists an element a of the antichain 
such that a belongs to c.\<close>

lemma card_ac_cv_eq: assumes "finite P"
                         and "chain_cover_on P cv"
                         and "antichain_on P  ac"
                         and "card cv = card ac"
                       shows "\<forall> c \<in> cv. \<exists> a \<in> ac. a \<in> c"
proof (rule ccontr)
  assume "\<not> (\<forall>c\<in>cv. \<exists>a\<in>ac. a \<in> c)"
  then obtain c where "c \<in> cv" "\<forall> a \<in> ac. a \<notin> c" by blast
  then have "\<forall> a \<in> ac. a \<in> \<Union> (cv - {c})" (is "\<forall> a \<in> ac. a \<in> ?cv_c")
    using assms(2,3) unfolding chain_cover_on_def antichain_on_def by blast
  then have 1: "ac \<subseteq> ?cv_c" by blast
  have 2: "partial_order_on ?cv_c (relation_of (\<le>) ?cv_c)" 
    using assms(1) assms(3) partial_order_on_def
    by (simp add: partial_order_on_relation_ofI)
  then have ac_on_cv_v: "antichain_on ?cv_c  ac" 
    using 1 assms(3) antichain_on_def unfolding antichain_on_def by blast
  have 3: "\<forall> a \<in> (cv - {c}). a \<subseteq> ?cv_c" by auto
  have 4: "\<forall> a \<in> (cv - {c}). Complete_Partial_Order.chain (\<le>) a" using assms(2) 
    unfolding chain_cover_on_def chain_on_def 
    by (meson DiffD1 Union_upper chain_subset)  
  have 5: "\<forall> a \<in> (cv - {c}). chain_on a ?cv_c" using chain_on_def 2 3 4 
    by metis
  have "\<Union> (cv - {c}) = ?cv_c" by simp
  then have cv_on_cv_v: "chain_cover_on ?cv_c (cv - {c})" 
    using 5 chain_cover_on_def by simp
  have "card (cv - {c}) < card cv"
    by (metis \<open>c \<in> cv\<close> assms(1) assms(2) card_Diff1_less 
        chain_cover_on_def finite_UnionD)
  then have "card (cv - {c}) < card ac" using assms(4) by simp
  then show False using ac_on_cv_v cv_on_cv_v antichain_card_leq assms part_ord
    by (metis Diff_insert_absorb Diff_subset Set.set_insert Union_mono assms(2,4) 
        card_Diff1_less_iff card_seteq chain_cover_on_def rev_finite_subset)
qed

text \<open> The following lemma shows that if an element m from the minimal set is in a chain, it is less 
than or equal to all elements in the chain.\<close>

lemma e_minset_lesseq_e_chain: assumes "chain_on c P" 
                                   and "is_minimal_in_set P m" 
                                   and "m \<in> c"
                                 shows "\<forall> a \<in> c. m \<le> a"
proof-
  have 1: "c \<subseteq> P" using assms(1) unfolding chain_on_def  by simp
  then have "is_minimal_in_set c  m" using 1 assms(2,3) is_minimal_in_set_iff by auto

  then have 3: "\<forall> a \<in> c. (a \<le> m) \<longrightarrow> a = m" unfolding is_minimal_in_set_iff by auto
  have "\<forall> a \<in> c. \<forall> b \<in> c. (a \<le> b) \<or> (b \<le> a)" using assms(1) 
    unfolding chain_on_def chain_def by blast
  then show ?thesis using 3 assms(3) by blast
qed

text \<open>The following lemma shows that if an element m from the maximal set is in a chain, it is greater 
than or equal to all elements in the chain.\<close>

lemma e_chain_lesseq_e_maxset: assumes "chain_on c P" 
                                   and "is_maximal_in_set P m" 
                                   and "m \<in> c"
                                 shows "\<forall> a \<in> c. a \<le> m"
  using assms chainE chain_on_def is_maximal_in_set_iff local.less_le_not_le subsetD 
  by metis 

text \<open>The following lemma shows that for any two elements of an antichain, if they both belong to the same chain in 
the chain cover, they must be the same element.\<close>

lemma ac_to_c : assumes "finite P"
                    and "chain_cover_on P cv"
                    and "antichain_on P ac"
                  shows "\<forall> a \<in> ac. \<forall> b \<in> ac. \<exists> c \<in> cv. a \<in> c \<and> b \<in> c \<longrightarrow> a = b"
proof-
  show ?thesis 
    using assms chain_cover_on_def antichain_on_def
    unfolding chain_cover_on_def chain_on_def chain_def antichain_on_def antichain_def 
    by (meson assms(2,3) elem_ac_in_c subsetD)
qed

text \<open>The following lemma shows that for two finite sets, if their cardinalities are equal, then their 
cardinalities would remain equal after removing a single element from both sets.\<close>

lemma card_Diff1_eq: assumes "finite A"
                         and "finite B"
                         and "card A = card B"
                       shows "\<forall> a \<in> A. \<forall> b \<in> B. card (A - {a}) = card (B - {b})"
proof-
  show ?thesis using assms(3) by auto
qed

text \<open>The following lemma shows that for two finite sets A and B of equal cardinality, removing two unique elements 
from A and one element from B will ensure the cardinality of A is less than B.\<close>

lemma card_Diff2_1_less: assumes "finite A"
                             and "finite B"
                             and "card A = card B"
                             and "a \<in> A"
                             and "b \<in> A"
                             and "a \<noteq> b"
                           shows "\<forall> x \<in> B. card ((A - {a}) - {b}) < card (B - {x})"
proof-
  show ?thesis
    by (metis DiffI assms card_Diff1_eq card_Diff1_less_iff finite_Diff singletonD)
qed

text \<open>The following lemma shows that for all elements of a partially ordered set, there exists an element in the 
minimal set that will be less than or equal to it.\<close>

lemma min_elem_for_P: assumes "finite P"
                        shows "\<forall> p \<in> P. \<exists> m. is_minimal_in_set P m \<and> m \<le> p" 
proof
  fix p
  assume asm:"p \<in> P"
  obtain m where m: "m \<in> P"  "m \<le> p" "\<forall>a \<in> P. a \<le> m \<longrightarrow> a = m"
    using finite_has_minimal2[OF assms(1) asm] by metis 
  hence "is_minimal_in_set P m" unfolding  is_minimal_in_set_iff 
    using part_ord by force
  then show "\<exists>m. is_minimal_in_set P m \<and> m \<le> p" using m 
    by blast
qed

text \<open> The following lemma shows that for all elements of a partially ordered set, there exists an element 
in the maximal set that will be greater than or equal to it.\<close>

lemma max_elem_for_P: assumes "finite P"
  shows "\<forall> p \<in> P. \<exists> m. is_maximal_in_set P m \<and> p \<le> m" 
  using assms finite_has_maximal2
  by (metis dual_order.strict_implies_order  is_maximal_in_set_iff)

text \<open> The following lemma shows that if the minimal set is not considered as the largest antichain on a set, 
then there exists an element a in the minimal set such that a does not belong to the
 largest antichain.\<close>

lemma min_e_nIn_lac: assumes "largest_antichain_on P ac"
                         and "{x. is_minimal_in_set P x} \<noteq> ac"
                         and "finite P"
                       shows "\<exists>m. (is_minimal_in_set P m) \<and> (m \<notin> ac)"
                          (is "\<exists>m. (?ms m) \<and> (m \<notin> ac)")
proof (rule ccontr)
  assume asm:"\<not> (\<exists> m. (?ms m) \<and> (m \<notin> ac))"
  then have "\<forall> m. \<not>(?ms m) \<or>  m \<in> ac" by blast
  then have 1: "{m . ?ms m} \<subseteq> ac" by blast
  then show False
  proof cases
    assume "{m . ?ms m} = ac"
    then show ?thesis using assms(2) by blast
  next
    assume "\<not> ({m . ?ms m} = ac)"
    then have 1:"{m . ?ms m} \<subset> ac" using 1 by simp
    then obtain y where y_def: "y \<in> ac" "?ms y" using asm assms(1,3)
      by (metis chain_cover_null elem_ac_in_c empty_subsetI ex_in_conv 
                largest_antichain_on_def local.ex_minimal_in_set psubsetE)
    then have y_in_P: "y \<in> P"
      using y_def(1) assms(1) largest_antichain_on_def antichain_on_def by blast
    then have 2: "\<forall> x. (?ms x \<longrightarrow> x \<noteq> y)" using y_def(2) 1 assms(1,3)
      using asm min_elem_for_P  DiffE mem_Collect_eq psubset_imp_ex_mem subset_iff
      unfolding largest_antichain_on_def antichain_def antichain_on_def
      by (smt (verit)) 
    have partial_P: "partial_order_on P (relation_of (\<le>) P)"
      using assms(1) largest_antichain_on_def antichain_on_def by simp
    then have "\<forall> x. ?ms x \<longrightarrow> \<not> (y \<le> x)" using 2 unfolding  is_minimal_in_set_iff
      using \<open>y \<in> P\<close> 
      using "2" y_def(2) by blast
    then show False using y_def(2) by blast
  qed
qed

text \<open> The following lemma shows that if the maximal set is not considered as the largest antichain on a set, 
then there exists an element a in the maximal set such that a does not belong to the 
largest antichain.\<close>

lemma max_e_nIn_lac: assumes "largest_antichain_on P ac"
                         and "{x . is_maximal_in_set P x} \<noteq> ac"
                         and "finite P"
                       shows "\<exists> m . is_maximal_in_set P m \<and>  m \<notin> ac"
                         (is "\<exists> m. ?ms m \<and> m \<notin> ac")
proof (rule ccontr)
  assume asm:"\<not> (\<exists> m. ?ms m \<and> m \<notin> ac)"
  then have "\<forall> m . \<not> ?ms m \<or> m \<in> ac" by blast
  then have 1: "{x . ?ms x} \<subseteq> ac" by blast
  then show False
  proof cases
    assume asm: "{x . ?ms x} = ac"
    then show ?thesis using assms(2) by blast
  next
    assume "\<not> ({x . ?ms x} = ac)"
    then have "{x . ?ms x} \<subset> ac" using 1 by simp
    then obtain y where y_def: "y \<in> ac" "\<not> (?ms y)" using assms asm
      by blast
    then have y_in_P: "y \<in> P"
      using y_def(1) assms(1) largest_antichain_on_def antichain_on_def by blast
    then have 2: "\<forall> x . ?ms x  \<longrightarrow> x \<noteq> y" using y_def(2) by auto
    have partial_P: "partial_order_on P (relation_of (\<le>) P)"
      using assms(1) largest_antichain_on_def antichain_on_def by simp
    then have "\<forall> x . ?ms x  \<longrightarrow> \<not> (x \<le> y)" using 2 unfolding  is_maximal_in_set_iff
      using \<open>y \<in> P\<close> 
      using local.dual_order.order_iff_strict by auto
    then have 3: "\<forall> x . ?ms x  \<longrightarrow> (x > y) \<or> \<not> (x \<le> y)" by blast
    then show False
    proof cases
      assume asm1: "\<exists> x. ?ms x \<and> (x > y)"
      have "\<forall> x \<in> ac. (x \<le> y) \<or> (y \<le> x) \<longrightarrow> x = y" using assms(1) y_def(1)
        unfolding largest_antichain_on_def antichain_on_def antichain_def by simp
      then have "\<forall> x . ?ms x  \<longrightarrow> (x > y) \<longrightarrow> x = y" using 1 by auto
      then have "\<exists> x. ?ms x \<and> y = x" using asm1 by auto
      then show ?thesis using 2 by blast
    next
      assume "\<not> (\<exists> x.  ?ms x \<and> (x > y))"
      then have "\<forall> x.  ?ms x \<longrightarrow> \<not> (x \<le> y)" using 3 by simp
      have a: "\<exists> z .  ?ms z \<and> y \<le> z" 
        using max_elem_for_P[OF assms(3)] y_in_P  partial_P 
        by fastforce
        
      have "\<forall> a. ?ms a  \<longrightarrow> (a \<le> y) \<or> (y \<le> a) \<longrightarrow> a = y" using assms(1) y_def(1) 1
        unfolding largest_antichain_on_def antichain_on_def antichain_def by blast
      then have "\<exists> z .?ms z \<and> z = y" using a by blast
      then show ?thesis using 2 by blast
    qed
  qed
qed

subsection "Statement and Proof"

text \<open> Proves theorem for the empty set.\<close>

lemma largest_antichain_card_eq_empty: 
  assumes "largest_antichain_on P lac"
      and "P = {}"
    shows "\<exists> cv. (chain_cover_on P cv) \<and> (card cv = card lac)"
proof-
  have "lac = {}" using assms(1) assms(2) 
    unfolding largest_antichain_on_def antichain_on_def by simp
  then show ?thesis using assms(2) chain_cover_null by auto
qed


text \<open> Proves theorem for the non-empty set.\<close>

lemma largest_antichard_card_eq: 
           assumes asm1: "largest_antichain_on P lac"
               and asm2: "finite P"
               and asm3: "P \<noteq> {}"
             shows "\<exists> cv. (chain_cover_on P cv) \<and> (card cv = card lac)"
  using assms
\<comment>\<open>Proof by induction on the cardinality of P\<close>
proof (induction "card P" arbitrary: P lac rule: less_induct)
  case less
  let ?max = "{x . is_maximal_in_set P x}"
  let ?min = "{x . is_minimal_in_set P x}"
  have partial_P: "partial_order_on P (relation_of (\<le>) P)" 
    using assms partial_order_on_def antichain_on_def largest_antichain_on_def 
          less.prems(1) by presburger
  show ?case \<comment>\<open>the largest antichain is not the maximal set or the minimal set\<close>
  proof (cases "\<exists> ac. (antichain_on P ac \<and> ac \<noteq> ?min \<and> ac \<noteq> ?max) \<and> card ac = card lac")
    case True
    obtain ac where ac:"antichain_on P ac" "ac \<noteq> ?min" "ac \<noteq> ?max" "card ac = card lac"
      using True by force
    then have "largest_antichain_on P ac" using asm1 largest_antichain_on_def
        using less.prems(1) by presburger
    then have lac_in_P: "lac \<subseteq> P" 
      using asm1 antichain_on_def largest_antichain_on_def less.prems(1) by presburger
    then have ac_in_P: "ac \<subseteq> P"
      using ac(1) antichain_on_def by blast
    define p_plus where "p_plus = {x. x \<in> P \<and> (\<exists> y \<in> ac.  y \<le> x)} "  
      \<comment>\<open>set of all elements greater than or equal to any given element in the largest 
      antichain\<close>
    define p_minus where "p_minus = {x. x \<in> P \<and> (\<exists> y \<in> ac.  x  \<le> y)}"
      \<comment>\<open>set of all elements less than or equal to any given element
                                 in the largest antichain\<close>
    have 1: "ac \<subseteq> p_plus" 
      \<comment>\<open>Shows that the largest antichain is a subset of p plus\<close>
      unfolding p_plus_def 
    proof
      fix x
      assume a1: "x \<in> ac"
      then have a2: "x \<in> P"
        using asm1 largest_antichain_on_def antichain_on_def less.prems(1) ac by blast
      then have "x \<le> x" using antichain_def by auto
      then show "x \<in> {x \<in> P. \<exists> y \<in> ac. y \<le> x}" using a1 a2 by auto
    qed
    have 2: "ac \<subseteq> p_minus" 
      \<comment>\<open>Shows that the largest antichain is a subset of p min\<close>
      unfolding p_minus_def 
    proof
      fix x
      assume a1: "x \<in> ac"
      then have a2: "x \<in> P" 
        using asm1 largest_antichain_on_def antichain_on_def less.prems(1) ac by blast
      then have "x \<le> x" using antichain_def by auto
      then show "x \<in> {x \<in> P. \<exists> y \<in> ac. x \<le> y}" using a1 a2 by auto
    qed
    have lac_subset: "ac \<subseteq> (p_plus \<inter> p_minus)" using 1 2 by simp
    have subset_lac: "(p_plus \<inter> p_minus) \<subseteq> ac"
    proof
      fix x
      assume "x \<in> (p_plus \<inter> p_minus)"
      then obtain a b where antichain_elems: "a \<in> ac" "b \<in> ac" "a \<le> x" "x \<le> b" 
        using p_plus_def p_minus_def by auto
      then have "a \<le> b" by simp
      then have "a = b" 
        using antichain_elems(1) antichain_elems(2) less.prems
          asm1 largest_antichain_on_def antichain_on_def antichain_def ac by metis
      then have "(a \<le> x) \<and> (x \<le> a)" 
        using antichain_elems(3) antichain_elems(4) by blast
      then have "x = a" by fastforce
      then show "x \<in> ac" using antichain_elems(1) by simp
    qed
    then have lac_pset_eq: "ac = (p_plus \<inter> p_minus)" using lac_subset by simp
    have P_PP_PM: "(p_plus \<union> p_minus) = P"
    proof
      show "(p_plus \<union> p_minus) \<subseteq> P"
      proof
        fix x
        assume "x \<in> (p_plus \<union> p_minus)"
        then have "x \<in> p_plus \<or> x \<in> p_minus" by simp
        then have "x \<in> P" using p_plus_def p_minus_def by auto
        then show "x \<in> P" .
      qed
    next
      show "P \<subseteq> (p_plus \<union> p_minus)"
      proof
        fix x
        assume x_in: "x \<in> P"
        then have "x \<in> ac \<or> x \<notin> ac" by simp
        then have "x \<in> (p_plus \<union> p_minus)"
        proof (cases "x \<in> ac")
          case True
          then show ?thesis using lac_subset by blast
        next
          case False
          then obtain y where "y \<in> ac" "(x \<le> y) \<or> (y \<le> x)" 
            using asm1 False x_in  asm2
             less.prems(1) less.prems(2) 
             \<open>largest_antichain_on P ac\<close> x_in x_not_in_ac_rel by blast
          then have "(x \<in> p_plus) \<or> (x \<in> p_minus)" 
            unfolding p_plus_def p_minus_def using x_in by auto
          then show ?thesis by simp
        qed
        then show "x \<in> p_plus \<union> p_minus" by simp
      qed
    qed
    obtain a where a_def: "a \<in> ?min" "a \<notin> ac" 
      using asm1 ac True asm3 less.prems(1) less.prems(2) min_e_nIn_lac
      by (metis \<open>largest_antichain_on P ac\<close> mem_Collect_eq)
    then have "\<forall> x \<in> ac. \<not> (x \<le> a)" 
      unfolding is_minimal_in_set_iff using partial_P lac_in_P 
      using ac(1) antichain_on_def 
      using local.nless_le by auto
    then have a_not_in_PP: "a \<notin> p_plus" using p_plus_def by simp
    have "a \<in> P" using a_def 
      by (simp add: local.is_minimal_in_set_iff)
    then have ppl: "card p_plus < card P" using P_PP_PM a_not_in_PP
      by (metis Un_upper1 card_mono card_subset_eq less.prems(2) 
          order_le_imp_less_or_eq)
    have p_plus_subset: "p_plus \<subseteq> P" using p_plus_def by simp
    have antichain_lac: "antichain ac" 
      using assms(1) less.prems ac 
      unfolding largest_antichain_on_def antichain_on_def by simp
    have finite_PP: "finite p_plus" using asm3  p_plus_subset finite_def
      using less.prems(2) rev_finite_subset by blast
    have finite_lac: "finite ac" using ac_in_P asm3 finite_def
      using finite_subset less.prems(2) ac   by auto
    have partial_PP: "partial_order_on p_plus (relation_of (\<le>) p_plus)" 
      using partial_P p_plus_subset partial_order_on_def
      by (smt (verit, best) local.antisym_conv local.le_less local.order_trans 
          partial_order_on_relation_ofI)
    then have lac_on_PP: "antichain_on p_plus ac" 
      using antichain_on_def 1 antichain_lac by simp
    have card_ac_on_P: "\<forall> ac. antichain_on P ac \<longrightarrow> card ac \<le> card ac"
      using asm1 largest_antichain_on_def less.prems(1) by auto
    then have "\<forall> ac. antichain_on p_plus  ac \<longrightarrow> card ac \<le> card ac"
      using p_plus_subset antichain_on_def largest_antichain_on_def
      by (meson partial_P preorder_class.order_trans)
    then have "largest_antichain_on p_plus ac" 
      using lac_on_PP unfolding largest_antichain_on_def 
      by (meson \<open>largest_antichain_on P  ac\<close> antichain_on_def 
          largest_antichain_on_def p_plus_subset preorder_class.order_trans)
    then have cv_PP: "\<exists>cv. chain_cover_on p_plus  cv \<and> card cv = card ac" 
      using less ppl by (metis "1" card.empty chain_cover_null finite_PP subset_empty)
    then obtain cvPP where cvPP_def: "chain_cover_on p_plus cvPP" 
            "card cvPP = card ac"
     using ac(4) by auto
    obtain b where b_def: "b \<in> ?max" "b \<notin> ac"
      using asm1 True asm3 less.prems(1) less.prems(2) max_e_nIn_lac 
      using \<open>largest_antichain_on P ac\<close> ac(3) by blast 
    then have "\<forall> x \<in> ac. \<not> (b \<le> x)" 
      unfolding  is_maximal_in_set_iff using partial_P ac_in_P
      nless_le by auto 
    then have b_not_in_PM: "b \<notin> p_minus" using p_minus_def by simp
    have "b \<in> P" using b_def is_maximal_in_set_iff  by blast
    then have pml: "card p_minus < card P" using  b_not_in_PM
      by (metis P_PP_PM Un_upper2 card_mono card_subset_eq less.prems(2) nat_less_le)
    have p_min_subset: "p_minus \<subseteq> P" using p_minus_def by simp
    have finite_PM: "finite p_minus" using asm3 p_min_subset finite_def
      using less.prems(2) rev_finite_subset by blast
    have partial_PM: "partial_order_on p_minus (relation_of (\<le>) p_minus)"
      by (simp add: partial_order_on_relation_ofI)
    then have lac_on_PM: "antichain_on p_minus ac" 
      using 2 antichain_lac antichain_on_def by simp
    then have "\<forall> ac. antichain_on p_minus  ac \<longrightarrow> card ac \<le> card ac"
      using card_ac_on_P P_PP_PM antichain_on_def largest_antichain_on_def
      by (metis partial_P sup.coboundedI2)
    then have "largest_antichain_on p_minus ac" 
      using lac_on_PM \<open>largest_antichain_on P ac\<close> antichain_on_def
            largest_antichain_on_def p_min_subset preorder_class.order_trans  
      by meson
    then have cv_PM: "\<exists>cv. chain_cover_on p_minus cv \<and> card cv = card ac" 
      using less pml P_PP_PM \<open>a \<in> P\<close> a_not_in_PP finite_PM 
      by blast
    then obtain cvPM where cvPM_def: 
                 "chain_cover_on p_minus cvPM" 
                 "card cvPM = card ac" 
      by auto 
    have lac_minPP: "ac = {x . is_minimal_in_set  p_plus x}" (is "ac = ?msPP")
    proof
      show "ac \<subseteq> {x . is_minimal_in_set  p_plus x}"
      proof
        fix x
        assume asm1: "x \<in> ac"
        then have x_in_PP: "x \<in> p_plus" using 1 by auto
        obtain y where y_def: "y \<in> p_plus" "y \<le> x"
          using 1 asm1 by blast
        then obtain a where a_def: "a \<in> ac" "a \<le> y" using p_plus_def by auto
        then have 0: "a \<in> p_plus" using 1 by auto
        then have I: "a \<le> x" using a_def y_def(2) by simp
        then have II: "a = x" using asm1 a_def(1) antichain_lac unfolding antichain_def by simp
        then have III: "y = x" using y_def(2) a_def(2) by simp
        have "\<forall> p \<in> p_plus. (p \<le> x) \<longrightarrow> p = x"
        proof
          fix p
          assume asmP: "p \<in> p_plus"
          show "p \<le> x \<longrightarrow> p = x"
          proof
            assume "p \<le> x"
            then show "p = x" 
              using asmP p_plus_def II a_def(1) antichain_def antichain_lac 
                    local.dual_order.antisym local.order.trans mem_Collect_eq
              by (smt (verit))
          qed
        qed
        then have "is_minimal_in_set p_plus x" using is_minimal_in_set_iff 
          using partial_PP 
          using x_in_PP by auto
        then show "x \<in> {x . is_minimal_in_set p_plus  x} " 
          using x_in_PP  
          using \<open>\<forall>p\<in>p_plus. p \<le> x \<longrightarrow> p = x\<close> local.is_minimal_in_set_iff by force
      qed
    next
      show "{x . is_minimal_in_set  p_plus x} \<subseteq> ac"
      proof
        fix x
        assume asm2: "x \<in> {x . is_minimal_in_set  p_plus x}"
        then have I: "\<forall> a \<in> p_plus. (a \<le> x) \<longrightarrow> a = x" 
          using is_minimal_in_set_iff
          by (metis dual_order.not_eq_order_implies_strict  mem_Collect_eq)
        have "x \<in> p_plus" using asm2 
          by (simp add: local.is_minimal_in_set_iff)
        then obtain y where y_def: "y \<in> ac" "y \<le> x" using p_plus_def by auto
        then have "y \<in> p_plus" using 1 by auto
        then have "y = x" using y_def(2) I by simp
        then show "x \<in> ac" using y_def(1) by simp
      qed
    qed
    then have card_msPP: "card ?msPP = card ac" by simp
    then have cvPP_elem_in_lac: "\<forall> m \<in> ?msPP. \<exists> c \<in> cvPP. m \<in> c" 
      using cvPP_def(1) partial_PP asm3 p_plus_subset 
            elem_minset_in_chain elem_ac_in_c 
         lac_on_PP 
      by (simp add: lac_minPP)
    then have cv_for_msPP: "\<forall> m \<in> ?msPP. \<exists> c \<in> cvPP. (\<forall> a \<in> c. m \<le> a)" 
      using elem_minset_in_chain partial_PP assms(3)
            cvPP_def(1) e_minset_lesseq_e_chain 
      unfolding  chain_cover_on_def[of "p_plus" cvPP] 
      by fastforce
    have lac_elem_in_cvPP: "\<forall> c \<in> cvPP. \<exists> m \<in> ?msPP. m \<in> c" 
      using cvPP_def card_msPP minset_ac card_ac_cv_eq
      by (metis P_PP_PM finite_Un lac_minPP lac_on_PP less.prems(2))
    then have "\<forall> c \<in> cvPP. \<exists> m \<in> ?msPP. (\<forall> a \<in> c. m \<le> a)" 
      using e_minset_lesseq_e_chain chain_cover_on_def cvPP_def(1) 
      by (metis mem_Collect_eq)
    then have cvPP_lac_rel: "\<forall> c \<in> cvPP. \<exists> x \<in> ac. (\<forall> a \<in> c. x \<le> a)"
      using lac_minPP by simp
    have lac_maxPM: "ac = {x . is_maximal_in_set p_minus x}" (is "ac = ?msPM")
    proof
      show "ac \<subseteq> ?msPM"
      proof
        fix x
        assume asm1: "x \<in> ac"
        then have x_in_PM: "x \<in> p_minus" using 2 by auto
        obtain y where y_def: "y \<in> p_minus" "x \<le> y"
          using 2 asm1 by blast
        then obtain a where a_def: "a \<in> ac" "y \<le> a" using p_minus_def by auto
        then have I: "x \<le> a" using y_def(2) by simp
        then have II: "a = x" 
          using asm1 a_def(1) antichain_lac unfolding antichain_def by simp
        then have III: "y = x" using y_def(2) a_def(2) by simp
        have "\<forall> p \<in> p_minus. (x \<le> p) \<longrightarrow> p = x"
        proof
          fix p
          assume asmP: "p \<in> p_minus"
          show "x \<le> p \<longrightarrow> p = x"
          proof
            assume "x \<le> p"
            then show "p = x" 
              using p_minus_def  II a_def(1) antichain_def antichain_lac asmP 
                    dual_order.antisym order.trans mem_Collect_eq
              by (smt (verit))
          qed
        qed
        then have "is_maximal_in_set p_minus x" 
          using partial_PM is_maximal_in_set_iff x_in_PM by force
        then show " x \<in> {x. is_maximal_in_set p_minus x}" 
          using x_in_PM  by auto
      qed
    next
      show "?msPM \<subseteq> ac"
      proof
        fix x
        assume asm2: "x \<in> {x . is_maximal_in_set p_minus x}"
        then have I: "\<forall> a \<in> p_minus. (x \<le> a) \<longrightarrow> a = x" 
          unfolding  is_maximal_in_set_iff by fastforce
        have "x \<in> p_minus" using asm2 
          by (simp add: local.is_maximal_in_set_iff)
        then obtain y where y_def: "y \<in> ac" "x \<le> y" using p_minus_def by auto
        then have "y \<in> p_minus" using 2 by auto
        then have "y = x" using y_def(2) I by simp
        then show "x \<in> ac" using y_def(1) by simp
      qed
    qed
    then have card_msPM: "card ?msPM = card ac" by simp
    then have cvPM_elem_in_lac: "\<forall> m \<in> ?msPM. \<exists> c \<in> cvPM. m \<in> c" 
      using cvPM_def(1) partial_PM asm3 p_min_subset elem_maxset_in_chain 
            elem_ac_in_c lac_maxPM lac_on_PM 
      by presburger
    then have cv_for_msPM: "\<forall> m \<in> ?msPM. \<exists> c \<in> cvPM. (\<forall> a \<in> c. a \<le> m)"
      using elem_maxset_in_chain partial_PM assms(3) cvPM_def(1) 
            e_chain_lesseq_e_maxset 
      unfolding chain_cover_on_def[of "p_minus" cvPM] 
      by (metis mem_Collect_eq)
    have lac_elem_in_cvPM: "\<forall> c \<in> cvPM. \<exists> m \<in> ?msPM. m \<in> c" 
      using cvPM_def card_msPM 
        maxset_ac card_ac_cv_eq finite_subset lac_maxPM lac_on_PM less.prems(2) 
        p_min_subset partial_PM
        by metis
      then have "\<forall> c \<in> cvPM. \<exists> m \<in> ?msPM. (\<forall> a \<in> c. a \<le> m)" 
        using e_chain_lesseq_e_maxset chain_cover_on_def cvPM_def(1) 
        by (metis mem_Collect_eq)
    then have cvPM_lac_rel: "\<forall> c \<in> cvPM. \<exists> x \<in> ac. (\<forall> a \<in> c. a \<le> x)" 
      using lac_maxPM by simp
    obtain x cp cm where x_cp_cm: "x \<in> ac" "cp \<in> cvPP" "(\<forall> a \<in> cp. x \<le> a)" 
                                  "cm \<in> cvPM" "(\<forall> a \<in> cm. a \<le> x)"
      using cv_for_msPP cv_for_msPM lac_minPP lac_maxPM assms(1) 
      unfolding largest_antichain_on_def antichain_on_def antichain_def
      by (metis P_PP_PM Sup_empty Un_empty_right all_not_in_conv chain_cover_on_def 
                cvPM_def(1) cvPP_def(1) cvPP_lac_rel lac_elem_in_cvPM less.prems(3))

    have "\<exists> f. \<forall> cp \<in> cvPP. \<exists> x \<in> ac. f cp = x \<and> x \<in> cp"
\<comment>\<open>defining a function that maps chains in the p plus chain cover to the element in
 the largest antichain that belongs to the chain.\<close>
      using lac_elem_in_cvPP lac_minPP by metis
    then obtain f where f_def: "\<forall> cp \<in> cvPP. \<exists> x \<in> ac. f cp = x \<and> x \<in> cp" by blast
    have lac_image_f: "f ` cvPP = ac"
    proof
      show "(f ` cvPP) \<subseteq> ac"
      proof
        fix y
        assume "y \<in> (f ` cvPP)"
        then obtain x where "f x = y" "x \<in> cvPP" using f_def by blast
        then have "y \<in> x" using f_def by blast
        then show "y \<in> ac" using f_def \<open>f x = y\<close> \<open>x \<in> cvPP\<close> by blast
      qed
    next
      show "ac \<subseteq> (f ` cvPP)"
      proof
        fix y
        assume y_in_lac: "y \<in> ac"
        then obtain x where "x \<in> cvPP" "y \<in> x" 
          using cvPP_elem_in_lac lac_minPP by auto
        then have "f x = y" using f_def y_in_lac
          by (metis antichain_def antichain_lac cvPP_lac_rel)
        then show "y \<in> (f ` cvPP)" using \<open>x \<in> cvPP\<close> by auto
      qed
    qed
    have "\<forall> x \<in> cvPP. \<forall> y \<in> cvPP. f x = f y \<longrightarrow> x = y"
    proof (rule ccontr)
      assume "\<not> (\<forall>x\<in>cvPP. \<forall>y\<in>cvPP. f x = f y \<longrightarrow> x = y)"
      then have "\<exists> x \<in> cvPP. \<exists> y \<in> cvPP. f x = f y \<and> x \<noteq> y" by blast
      then obtain z x y where z_x_y: "x \<in> cvPP" "y \<in> cvPP" "x \<noteq> y" "z = f x" "z = f y" 
        by blast
      then have z_in: "z \<in> ac" using f_def by blast
      then have "\<forall> a \<in> ac. (a \<in> x \<or> a \<in> y) \<longrightarrow> a = z" 
        using ac_to_c partial_P asm3 p_plus_subset cvPP_def(1) 
              lac_on_PP z_x_y(1) z_x_y(2)
        by (metis antichain_def antichain_lac cvPP_lac_rel f_def z_x_y(4) z_x_y(5))
      then have "\<forall> a \<in> ac. a \<noteq> z \<longrightarrow> a \<notin> x \<and> a \<notin> y" by blast
      then have "\<forall> a \<in> (ac - {z}). a \<in> \<Union> ((cvPP - {x}) - {y})" 
        using cvPP_def(1) 1 unfolding chain_cover_on_def by blast
      then have a: "(ac - {z}) \<subseteq> \<Union> ((cvPP - {x}) - {y})" (is "?lac_z \<subseteq> ?cvPP_xy") by blast
      have b: "partial_order_on ?cvPP_xy (relation_of (\<le>) ?cvPP_xy)"
        using partial_PP cvPP_def(1) partial_order_on_def 
              dual_order.eq_iff dual_order.eq_iff 
              dual_order.trans partial_order_on_relation_ofI 
              dual_order.trans partial_order_on_relation_ofI
        by (smt (verit))
      then have ac_on_cvPP_xy: "antichain_on ?cvPP_xy ?lac_z" 
        using a lac_on_PP antichain_on_def unfolding antichain_on_def
        by (metis DiffD1 antichain_def antichain_lac)
      have c: "\<forall> a \<in> ((cvPP - {x}) - {y}). a \<subseteq> ?cvPP_xy" by auto
      have d: "\<forall> a \<in> ((cvPP - {x}) - {y}). Complete_Partial_Order.chain (\<le>) a" using cvPP_def(1)
        unfolding chain_cover_on_def chain_on_def 
        using z_x_y(2) by blast 
      have e: "\<forall> a \<in> ((cvPP - {x}) - {y}). chain_on  a ?cvPP_xy" 
        using b c d chain_on_def 
        by (metis Diff_iff Sup_upper chain_cover_on_def cvPP_def(1))  
      have f: "finite ?cvPP_xy" using finite_PP cvPP_def(1) 
        unfolding chain_cover_on_def chain_on_def
        by (metis (no_types, opaque_lifting) Diff_eq_empty_iff Diff_subset 
                 Un_Diff_cancel Union_Un_distrib finite_Un)
      have "\<Union> ((cvPP - {x}) - {y}) = ?cvPP_xy" by blast
      then have cv_on: "chain_cover_on ?cvPP_xy ((cvPP - {x}) - {y})" 
        using chain_cover_on_def[of  ?cvPP_xy " ((cvPP - {x}) - {y}) "] 
              e chain_on_def by argo
      have "card ((cvPP - {x}) - {y}) < card cvPP" 
        using z_x_y(1) z_x_y(2) finite_PP cvPP_def(1) chain_cover_on_def finite_UnionD
        by (metis card_Diff2_less)
      then have "card ((cvPP - {x}) - {y}) < card (ac - {z})" 
        using cvPP_def(2) finite_PP finite_lac cvPP_def(1) chain_cover_on_def 
              finite_UnionD z_x_y(1) z_x_y(2) z_x_y(3) z_in card_Diff2_1_less 
        by metis
      then show False using antichain_card_leq ac_on_cvPP_xy cv_on f by fastforce
    qed
    then have inj_f: "inj_on f cvPP" using inj_on_def by auto
    then have bij_f: "bij_betw f cvPP ac" using lac_image_f bij_betw_def by blast
    have "\<exists> g. \<forall> cm \<in> cvPM. \<exists> x \<in> ac. g cm = x \<and> x \<in> cm"
      using lac_elem_in_cvPM lac_maxPM by metis
    then obtain g where g_def: "\<forall> cm \<in> cvPM. \<exists> x \<in> ac. g cm = x \<and> x \<in> cm" by blast
    have lac_image_g: "g ` cvPM = ac"
    proof
      show "g ` cvPM \<subseteq> ac"
      proof
        fix y 
        assume "y \<in> g ` cvPM"
        then obtain x where x: "g x = y" "x \<in> cvPM" using g_def by blast
        then have "y \<in> x" using g_def by blast
        then show "y \<in> ac" using g_def x by auto
      qed
    next
      show "ac \<subseteq> g ` cvPM"
      proof
        fix y
        assume y_in_lac: "y \<in> ac"
        then obtain x where x: "x \<in> cvPM" "y \<in> x" 
          using cvPM_elem_in_lac lac_maxPM by auto
        then have "g x = y" using g_def y_in_lac
          by (metis antichain_def antichain_lac cvPM_lac_rel)
        then show "y \<in> g ` cvPM" using x by blast
      qed
    qed
    have "\<forall> x \<in> cvPM. \<forall> y \<in> cvPM. g x = g y \<longrightarrow> x = y"
    proof (rule ccontr)
      assume "\<not> (\<forall>x\<in>cvPM. \<forall>y\<in>cvPM. g x = g y \<longrightarrow> x = y)"
      then have "\<exists> x \<in> cvPM. \<exists> y \<in> cvPM. g x = g y \<and> x \<noteq> y" by blast
      then obtain z x y where z_x_y: "x \<in> cvPM"  "y \<in> cvPM" 
                                     "x \<noteq> y" "z = g x" "z = g y" by blast
      then have z_in: "z \<in> ac" using g_def by blast
      then have "\<forall> a \<in> ac. (a \<in> x \<or> a \<in> y) \<longrightarrow> a = z" 
        using ac_to_c partial_P asm3 z_x_y(1) z_x_y(2)
        by (metis antichain_def antichain_lac cvPM_lac_rel g_def z_x_y(4) z_x_y(5))
      then have "\<forall> a \<in> ac. a \<noteq> z \<longrightarrow> a \<notin> x \<and> a \<notin> y" by blast
      then have "\<forall> a \<in> (ac - {z}). a \<in> \<Union> ((cvPM - {x}) - {y})" 
        using cvPM_def(1) 2 unfolding chain_cover_on_def by blast
      then have a: "(ac - {z}) \<subseteq> \<Union> ((cvPM - {x}) - {y})" (is "?lac_z \<subseteq> ?cvPM_xy") 
        by blast
      have b: "partial_order_on ?cvPM_xy (relation_of (\<le>) ?cvPM_xy)"
        using partial_PP partial_order_on_def
        by (smt (verit) local.dual_order.eq_iff 
            local.dual_order.trans partial_order_on_relation_ofI)
      then have ac_on_cvPM_xy: "antichain_on ?cvPM_xy ?lac_z" 
        using a antichain_on_def unfolding antichain_on_def
        by (metis DiffD1 antichain_def antichain_lac)
      have c: "\<forall> a \<in> ((cvPM - {x}) - {y}). a \<subseteq> ?cvPM_xy" by auto
      have d: "\<forall> a \<in> ((cvPM - {x}) - {y}). Complete_Partial_Order.chain (\<le>) a" 
        using cvPM_def(1)
        unfolding chain_cover_on_def chain_on_def 
        by (metis DiffD1) 
      have e: "\<forall> a \<in> ((cvPM - {x}) - {y}). chain_on a ?cvPM_xy" 
        using b c d chain_on_def 
        by (metis Diff_iff Union_upper chain_cover_on_def cvPM_def(1)) 
      have f: "finite ?cvPM_xy" using finite_PM cvPM_def(1) 
        unfolding chain_cover_on_def chain_on_def
        by (metis (no_types, opaque_lifting) Diff_eq_empty_iff Diff_subset
                  Un_Diff_cancel Union_Un_distrib finite_Un)
      have "\<Union> ((cvPM - {x}) - {y}) = ?cvPM_xy" by blast
      then have cv_on: "chain_cover_on ?cvPM_xy ((cvPM - {x}) - {y})" 
        using chain_cover_on_def e by simp
      have "card ((cvPM - {x}) - {y}) < card cvPM" 
        using z_x_y(1) z_x_y(2) finite_PM cvPM_def(1) chain_cover_on_def finite_UnionD
        by (metis card_Diff2_less)
      then have "card ((cvPM - {x}) - {y}) < card (ac - {z})" 
        using cvPM_def(2) finite_PM finite_lac cvPM_def(1) chain_cover_on_def 
              finite_UnionD z_x_y(1) z_x_y(2) z_x_y(3) z_in card_Diff2_1_less 
        by metis
      then show False using antichain_card_leq ac_on_cvPM_xy cv_on f by fastforce
    qed
    then have inj_g:  "inj_on g cvPM" using inj_on_def by auto
    then have bij_g: "bij_betw g cvPM ac" using lac_image_g bij_betw_def by blast
    define h where "h = inv_into cvPP f"
    then have bij_h: "bij_betw h ac cvPP" 
      using f_def bij_f bij_betw_inv_into by auto
    define i where "i = inv_into cvPM g"
    then have bij_i: "bij_betw i ac cvPM" 
      using g_def bij_f bij_g bij_betw_inv_into by auto
    obtain j where j_def: "\<forall> x \<in> ac. j x = (h x) \<union> (i x)" 
      using h_def i_def f_def g_def bij_h bij_i
      by (metis sup_apply)
    have "\<forall> x \<in> ac. \<forall> y \<in> ac. j x = j y \<longrightarrow> x = y"
    proof (rule ccontr)
      assume "\<not> (\<forall> x \<in> ac. \<forall> y \<in> ac. j x = j y \<longrightarrow> x = y)"
      then have "\<exists> x \<in> ac. \<exists> y \<in> ac. j x = j y \<and> x \<noteq> y" by blast
      then obtain z x y where z_x_y: "x \<in> ac" "y \<in> ac" "z = j x" "z = j y" "x \<noteq> y" 
        by auto 
      then have z_x: "z = (h x) \<union> (i x)" using j_def by simp
      have "z = (h y) \<union> (i y)" using j_def z_x_y by simp
      then have union_eq: "(h x) \<union> (i x) = (h y) \<union> (i y)" using z_x by simp
      have x_hx: "x \<in> (h x)" using h_def f_def bij_f bij_h
        by (metis bij_betw_apply f_inv_into_f lac_image_f z_x_y(1))
      have x_ix: "x \<in> (i x)" using i_def g_def bij_g bij_i
        by (metis bij_betw_apply f_inv_into_f lac_image_g z_x_y(1))
      have "y \<in> (h y)" using h_def f_def bij_f bij_h
        by (metis bij_betw_apply f_inv_into_f lac_image_f z_x_y(2))
      then have "y \<in> (h x) \<union> (i x)" using union_eq by simp
      then have y_in: "y \<in> (h x) \<or> y \<in> (i x)" by simp
      then show False
      proof (cases "y \<in> (h x)")
        case True
        have "\<exists> c \<in> cvPP. (h x) = c" using h_def f_def bij_h bij_f
          by (simp add: bij_betw_apply z_x_y(1))
        then obtain c where c_def: "c \<in> cvPP" "(h x) = c" by simp
        then have "x \<in> c \<and> y \<in> c" using x_hx True by simp
        then have "x = y" using z_x_y(1) z_x_y(2) asm1 c_def(1) cvPP_def less.prems ac
          unfolding largest_antichain_on_def antichain_on_def antichain_def 
                    chain_cover_on_def chain_on_def chain_def 
          by (metis)
        then show ?thesis using z_x_y(5) by simp
      next
        case False
        then have y_ix: "y \<in> (i x)" using y_in by simp
        have "\<exists> c \<in> cvPM. (i x) = c" using i_def g_def bij_i bij_g
          by (simp add: bij_betw_apply z_x_y(1))
        then obtain c where c_def: "c \<in> cvPM" "(i x) = c" by simp
        then have "x \<in> c \<and> y \<in> c" using x_ix y_ix by simp
        then have "x = y" 
          using z_x_y(1) z_x_y(2) asm1 ac c_def(1) cvPM_def less.prems 
          unfolding largest_antichain_on_def antichain_on_def antichain_def 
                    chain_cover_on_def chain_on_def chain_def 
          by (metis)
        then show ?thesis using z_x_y(5) by simp
      qed
    qed
    then have inj_j: "inj_on j ac" using inj_on_def by auto
    obtain cvf where cvf_def: "cvf = {j x | x . x \<in> ac}" by simp
    then have "cvf = j ` ac" by blast
    then have bij_j: "bij_betw j ac cvf" using inj_j bij_betw_def by auto
    then have card_cvf: "card cvf = card ac"
      by (metis bij_betw_same_card)
    have j_h_i: "\<forall> x \<in> ac. \<exists> cp \<in> cvPP. \<exists> cm \<in> cvPM. (h x = cp) \<and> (i x = cm) 
                        \<and> (j x = (cp \<union> cm))"
      using j_def bij_h bij_i by (meson bij_betwE)
    have "\<Union> cvf = (p_plus \<union> p_minus)"
    proof
      show "\<Union> cvf \<subseteq> (p_plus \<union> p_minus)"
      proof
        fix y
        assume "y \<in> \<Union> cvf"
        then obtain z where z_def: "z \<in> cvf" "y \<in> z" by blast
        then obtain cp cm where cp_cm: "cp \<in> cvPP" "cm \<in> cvPM" "z = (cp \<union> cm)" 
          using cvf_def h_def i_def j_h_i by blast
        then have "y \<in> cp \<or> y \<in> cm" using z_def(2) by simp
        then show "y \<in> (p_plus \<union> p_minus)" using cp_cm(1) cp_cm(2) cvPP_def cvPM_def
          unfolding chain_cover_on_def chain_on_def by blast
      qed
    next
      show "(p_plus \<union> p_minus) \<subseteq> \<Union> cvf"
      proof
        fix y
        assume "y \<in> (p_plus \<union> p_minus)"
        then have y_in: "y \<in> p_plus \<or> y \<in> p_minus" by simp
        have "p_plus = \<Union> cvPP \<and> p_minus = \<Union> cvPM" using cvPP_def cvPM_def
          unfolding chain_cover_on_def by simp
        then have "y \<in> (\<Union> cvPP) \<or> y \<in> (\<Union> cvPM)" using y_in by simp
        then have "\<exists> cp \<in> cvPP. \<exists> cm \<in> cvPM. (y \<in> cp) \<or> (y \<in> cm)" 
          using cvPP_def cvPM_def
          by (meson Union_iff x_cp_cm(2) x_cp_cm(4))
        then obtain cp cm where cp_cm: "cp \<in> cvPP" "cm \<in> cvPM" "y \<in> (cp \<union> cm)" by blast
        have 1: "\<exists> cm \<in> cvPM. \<exists> x \<in> ac. (x \<in> cp) \<and> (x \<in> cm)"
          using cp_cm(1) f_def cvPM_elem_in_lac lac_maxPM by metis
        have 2: "\<exists> cp \<in> cvPP. \<exists> x \<in> ac. (x \<in> cp) \<and> (x \<in> cm)"
          using cp_cm(2) g_def cvPP_elem_in_lac lac_minPP 
          by meson
        then show "y \<in> \<Union> cvf"
        proof (cases "y \<in> cp")
          case True
          obtain x cmc where x_cm: "x \<in> ac" "x \<in> cp" "x \<in> cmc" "cmc \<in> cvPM" 
            using 1 by blast
          have "f cp = x" using cp_cm(1) x_cm(1) f_def
            by (metis antichain_def antichain_lac cvPP_lac_rel x_cm(2))
          then have h_x: "h x = cp" using h_def cp_cm(1) inj_f by auto
          have "g cmc = x" using x_cm(4) x_cm(1) g_def
            by (metis antichain_def antichain_lac cvPM_lac_rel x_cm(3))
          then have i_x: "i x = cmc" using i_def
            by (meson bij_betw_inv_into_left bij_g x_cm(4))
          then have "j x = h x \<union> i x" using j_def x_cm(1) by simp
          then have "(h x \<union> i x) \<in> cvf" using cvf_def x_cm(1) by auto
          then have "(cp \<union> cmc) \<in> cvf" using h_x i_x by simp
          then show ?thesis using True by blast
        next
          case False
          then have y_in: "y \<in> cm" using cp_cm(3) by simp
          obtain x cpc where x_cp: "x \<in> ac" "x \<in> cm" "x \<in> cpc" "cpc \<in> cvPP" 
            using 2 by blast
          have "g cm = x" using cp_cm(2) x_cp(1) x_cp(2) g_def
            by (metis antichain_def antichain_lac cvPM_lac_rel)
          then have x_i: "i x = cm" using i_def x_cp(1)
            by (meson bij_betw_inv_into_left bij_g cp_cm(2))
          have "f cpc = x" using x_cp(4) x_cp(1) x_cp(3) f_def
            by (metis antichain_def antichain_lac cvPP_lac_rel)
          then have x_h: "h x = cpc" using h_def x_cp(1) inj_f x_cp(4) by force
          then have "j x = h x \<union> i x" using j_def x_cp(1) by simp
          then have "(h x \<union> i x) \<in> cvf" using cvf_def x_cp(1) by auto
          then have "(cpc \<union> cm) \<in> cvf" using x_h x_i by simp
          then show ?thesis using y_in by blast
        qed
      qed
    qed
    then have cvf_P: "\<Union> cvf = P" using P_PP_PM by simp
    have "\<forall> x \<in> cvf. chain_on x P"
    proof
      fix x
      assume asm1: "x \<in> cvf"
      then obtain a where a_def: "a \<in> ac" "j a = x" using cvf_def by blast
      then obtain cp cm where cp_cm: "cp \<in> cvPP" "cm \<in> cvPM" "h a = cp \<and> i a = cm" 
        using h_def i_def bij_h bij_i j_h_i by blast
      then have x_union: "x = (cp \<union> cm)" using j_def a_def by simp
      then have a_in: "a \<in> cp \<and> a \<in> cm" using cp_cm h_def f_def i_def g_def
        by (metis \<open>a \<in> ac\<close> bij_betw_inv_into_right bij_f bij_g)
      then have a_rel_cp: "\<forall> b \<in> cp. (a \<le> b)" 
        using a_def(1) cp_cm(1) lac_minPP e_minset_lesseq_e_chain 
        by (metis antichain_def antichain_lac cvPP_lac_rel)
      have a_rel_cm: "\<forall> b \<in> cm. (b \<le> a)"
        using a_def(1) cp_cm(2) lac_maxPM e_chain_lesseq_e_maxset a_in
        by (metis antichain_def antichain_lac cvPM_lac_rel)
      then have "\<forall> a \<in> cp. \<forall> b \<in> cm. (b \<le> a)" using a_rel_cp by fastforce
      then have "\<forall> x \<in> (cp \<union> cm). \<forall> y \<in> (cp \<union> cm). (x \<le> y) \<or> (y \<le> x)"
        using cp_cm(1) cp_cm(2) cvPP_def cvPM_def
        unfolding chain_cover_on_def chain_on_def chain_def 
        by (metis Un_iff) 
      then have "Complete_Partial_Order.chain (\<le>) (cp \<union> cm)" using chain_def by auto
      then have chain_x: "Complete_Partial_Order.chain (\<le>) x" using x_union by simp
      have "x \<subseteq> P" using cvf_P asm1 by blast
      then show "chain_on x P" using chain_x partial_P chain_on_def  by simp
    qed
    then have "chain_cover_on P cvf" using cvf_P  chain_cover_on_def[of P cvf]  by simp
    then show caseTrue: ?thesis using card_cvf ac by auto
  next \<comment>\<open>the largest antichain is equal to the maximal set or the minimal set\<close>
    case False
    assume "\<not> (\<exists> ac. (antichain_on P ac \<and> ac \<noteq> ?min \<and> ac \<noteq> ?max) \<and> card ac = card lac)" 
    then have "\<not> ((lac \<noteq> ?max) \<and> (lac \<noteq> ?min))" 
      using less(2) unfolding largest_antichain_on_def
      by blast
    then have max_min_asm: "(lac = ?max) \<or> (lac = ?min)" by simp
    then have caseAsm: 
      "\<forall> ac. (antichain_on P  ac \<and> ac \<noteq> ?min \<and> ac \<noteq> ?max) \<longrightarrow> card ac \<le> card lac"
      using asm1 largest_antichain_on_def less.prems(1) by presburger
    then have case2: "\<forall> ac. (antichain_on P  ac \<and> ac \<noteq> ?min \<and> ac \<noteq> ?max) \<longrightarrow> card ac < card lac" 
        using False by force
    obtain x where x: "x \<in> ?min" 
      using is_minimal_in_set_iff non_empty_minset partial_P assms(2,3)
      by (metis empty_Collect_eq less.prems(2) less.prems(3) mem_Collect_eq)
    then have "x \<in> P" using is_minimal_in_set_iff by simp
    then obtain y where y: "y \<in> ?max" "x \<le> y" using partial_P max_elem_for_P
        using less.prems(2) by blast
    define PD where PD_def: "PD = P - {x,y}"
    then have finite_PD: "finite PD" using asm3 finite_def
        by (simp add: less.prems(2))
    then have partial_PD: "partial_order_on PD (relation_of (\<le>) PD)" 
        using partial_P partial_order_on_def
        by (simp add: partial_order_on_relation_ofI)
    then have max_min_nPD: "\<not> (?max \<subseteq> PD) \<and> \<not> (?min \<subseteq> PD)" 
        using PD_def x y(1) by blast
    have a1: "\<forall> a \<in> P. (a \<noteq> x) \<and> (a \<noteq> y) \<longrightarrow> a \<in> PD" 
        using PD_def by blast
      then have "\<forall> a \<in> ?max. (a \<noteq> x) \<and> (a \<noteq> y) \<longrightarrow> a \<in> PD" 
        using  is_maximal_in_set_iff  by blast
    then have "(?max - {x, y}) \<subseteq> PD" (is "?maxPD \<subseteq> PD") by blast
    have card_maxPD: "card (?max - {x,y}) = (card ?max - 1)" using x y
      proof cases
        assume "x = y"
        then show ?thesis using y(1) by force
      next
        assume "\<not> (x = y)"
        then have "x < y" using y(2) by simp
        then have "\<not> (is_maximal_in_set P x)" using  x y(1) 
          using \<open>x \<noteq> y\<close> is_maximal_in_set_iff by fastforce
        then have "x \<notin> ?max"  by simp
        then show ?thesis using y(1) by auto
      qed
      have "\<forall> a \<in> ?min. (a \<noteq> x) \<and> (a \<noteq> y) \<longrightarrow> a \<in> PD" 
        using is_minimal_in_set_iff  a1 
        by (simp add: a1 local.is_minimal_in_set_iff)
    then have "(?min - {x, y}) \<subseteq> PD" (is "?minPD \<subseteq> PD") by blast
    have card_minPD: "card (?min - {x,y}) = (card ?min - 1)" using x y
    proof cases
      assume "x = y"
      then show ?thesis using x by auto
    next
      assume "\<not> (x = y)"
      then have "x < y" using y(2) by simp
      then have "\<not> (is_minimal_in_set P y)" using is_minimal_in_set_iff x y(1) 
          by force
      then have "y \<notin> ?min"  by simp
      then show ?thesis using x
          by (metis Diff_insert Diff_insert0 card_Diff_singleton_if)
    qed
    then show ?thesis
    proof cases
      assume asm:"lac = ?max" \<comment>\<open> case where the largest antichain is the maximal set\<close>
      then have card_maxPD: "card ?maxPD = (card lac - 1)" using card_maxPD by auto
      then have ac_less: "\<forall> ac. (antichain_on P  ac \<and> ac \<noteq> ?max \<and> ac \<noteq> ?min) 
                         \<longrightarrow> card ac \<le> (card lac - 1)" 
          using case2 by auto
      have PD_sub: "PD \<subset> P" using PD_def
          by (simp add: \<open>x \<in> P\<close> subset_Diff_insert subset_not_subset_eq)
      then have PD_less: "card PD < card P" using asm3 card_def
          by (simp add: less.prems(2) psubset_card_mono)
        have maxPD_sub: "?maxPD \<subseteq> PD" 
          using PD_def  \<open>{x. is_maximal_in_set P x} - {x, y} \<subseteq> PD\<close> by blast  
      have "?maxPD \<subseteq> ?max" by blast
      then have "antichain  ?maxPD" using maxset_ac unfolding antichain_def by blast
      then have ac_maxPD:  "antichain_on PD  ?maxPD" 
          using maxPD_sub antichain_on_def partial_PD by simp
      have acPD_nMax_nMin: "\<forall> ac . (antichain_on PD ac) \<longrightarrow> (ac \<noteq> ?max \<and> ac \<noteq> ?min)" 
          using max_min_nPD antichain_on_def 
          by auto
      have "\<forall> ac. (antichain_on PD  ac) \<longrightarrow> (antichain_on P  ac)"
          using antichain_on_def antichain_def
          by (meson PD_sub partial_P psubset_imp_subset subset_trans)
      then have "\<forall> ac. (antichain_on PD  ac) \<longrightarrow> card ac \<le> (card lac - 1)" 
          using ac_less PD_sub max_min_nPD acPD_nMax_nMin by blast
      then have maxPD_lac: "largest_antichain_on PD ?maxPD"
          using largest_antichain_on_def ac_maxPD card_maxPD by simp
      then have "\<exists> cv. chain_cover_on PD  cv \<and> card cv = card ?maxPD"
      proof cases
        assume "PD \<noteq> {}"
        then show ?thesis using less PD_less maxPD_lac finite_PD by blast
      next
        assume "\<not> (PD \<noteq> {})"
        then have PD_empty: "PD = {}" by simp
        then have "?maxPD = {}" using maxPD_sub by auto
        then show ?thesis 
          using maxPD_lac PD_empty largest_antichain_card_eq_empty by simp
      qed
      then obtain cvPD where cvPD_def: "chain_cover_on PD cvPD" 
                                       "card cvPD = card ?maxPD" by blast
      then have "\<Union> cvPD = PD" unfolding chain_cover_on_def by simp
      then have union_cvPD: "\<Union> (cvPD \<union> {{x,y}}) = P" using PD_def
          using \<open>x \<in> P\<close>  y(1) is_maximal_in_set_iff  by force 
      have chains_cvPD: "\<forall> x \<in> cvPD. chain_on x P" 
        using chain_on_def cvPD_def(1) PD_sub unfolding chain_cover_on_def
        by (meson subset_not_subset_eq subset_trans)
      have "{x,y} \<subseteq> P" using x y  
        using union_cvPD by blast
      then have xy_chain_on: "chain_on  {x,y} P" 
        using partial_P y(2) chain_on_def chain_def 
        by fast
      define cvf where cvf_def: "cvf = cvPD \<union> {{x,y}}"
      have cv_cvf: "chain_cover_on P cvf" 
        using chains_cvPD union_cvPD xy_chain_on unfolding chain_cover_on_def cvf_def
         by simp
      have "\<not> ({x,y} \<subseteq> PD)" using PD_def by simp
      then have "{x,y} \<notin> cvPD" using cvPD_def(1) 
          unfolding chain_cover_on_def chain_on_def by auto
      then have "card (cvPD \<union> {{x,y}}) = (card ?maxPD) + 1" using cvPD_def(2) card_def
          by (simp add: \<open>\<Union> cvPD = PD\<close> finite_PD finite_UnionD)
      then have "card cvf = (card ?maxPD) + 1" using cvf_def by auto
      then have "card cvf = card lac" using card_maxPD asm
        by (metis Diff_infinite_finite Suc_eq_plus1  \<open>{x, y} \<subseteq> P\<close> card_Diff_singleton 
            card_Suc_Diff1 finite_PD finite_subset less.prems(2) maxPD_sub y(1))
      then show ?thesis using cv_cvf by blast
    next
      assume "\<not> (lac = ?max)" 
      \<comment>\<open> complementary case where the largest antichain is the minimal set\<close>
      then have "lac = ?min" using max_min_asm by simp
      then have card_minPD: "card ?minPD = (card lac - 1)" using card_minPD by simp
      then have ac_less: "\<forall> ac. (antichain_on P ac \<and> ac \<noteq> ?max \<and> ac \<noteq> ?min) 
                         \<longrightarrow> card ac \<le> (card lac - 1)" 
          using case2 by auto
      have PD_sub: "PD \<subseteq> P" using PD_def by simp
      then have PD_less: "card PD < card P" using asm3
        using less.prems(2) max_min_nPD is_minimal_in_set_iff psubset_card_mono
        by (metis DiffE PD_def \<open>x \<in> P\<close> insertCI psubsetI) 
      have minPD_sub: "?minPD \<subseteq> PD" using PD_def unfolding  
        is_minimal_in_set_iff by blast
      have "?minPD \<subseteq> ?min" by blast
      then have "antichain ?minPD" using minset_ac is_minimal_in_set_iff
        unfolding antichain_def 
        by (metis DiffD1) 
      then have ac_minPD:  "antichain_on PD ?minPD" 
          using minPD_sub antichain_on_def partial_PD by simp
      have acPD_nMax_nMin: "\<forall> ac . (antichain_on PD ac) \<longrightarrow> (ac \<noteq> ?max \<and> ac \<noteq> ?min)" 
          using max_min_nPD antichain_on_def 
          by metis 
      have "\<forall> ac. (antichain_on PD ac) \<longrightarrow> (antichain_on P ac)"
          using antichain_on_def antichain_def
          by (meson PD_sub partial_P subset_trans)
      then have "\<forall> ac. (antichain_on PD  ac) \<longrightarrow> card ac \<le> (card lac - 1)" 
          using ac_less PD_sub max_min_nPD acPD_nMax_nMin by blast
      then have minPD_lac: "largest_antichain_on PD  ?minPD" 
        using largest_antichain_on_def ac_minPD card_minPD by simp
      then have "\<exists> cv. chain_cover_on PD cv \<and> card cv = card ?minPD"
      proof cases
        assume "PD \<noteq> {}"
        then show ?thesis using less PD_less minPD_lac finite_PD by blast
      next
        assume "\<not> (PD \<noteq> {})"
        then have PD_empty: "PD = {}" by simp
        then have "?minPD = {}" using minPD_sub by auto
        then show ?thesis 
          using minPD_lac PD_empty largest_antichain_card_eq_empty by simp
      qed
      then obtain cvPD where cvPD_def: "chain_cover_on PD cvPD" 
                                       "card cvPD = card ?minPD" by blast
      then have "\<Union> cvPD = PD" unfolding chain_cover_on_def by simp
      then have union_cvPD: "\<Union> (cvPD \<union> {{x,y}}) = P" using PD_def
          using \<open>x \<in> P\<close>  y(1) 
          using   is_maximal_in_set_iff by force
      have chains_cvPD: "\<forall> x \<in> cvPD. chain_on x P" 
          using chain_on_def cvPD_def(1) PD_sub unfolding chain_cover_on_def
          by (meson Sup_le_iff partial_P)
      have "{x,y} \<subseteq> P" using x y  using union_cvPD by blast
      then have xy_chain_on: "chain_on {x,y} P" 
          using partial_P y(2) chain_on_def chain_def by fast
      define cvf where cvf_def: "cvf = cvPD \<union> {{x,y}}"
      then have cv_cvf: "chain_cover_on P cvf" 
          using chains_cvPD union_cvPD xy_chain_on unfolding chain_cover_on_def by simp
      have "\<not> ({x,y} \<subseteq> PD)" using PD_def by simp
      then have "{x,y} \<notin> cvPD" using cvPD_def(1) 
          unfolding chain_cover_on_def chain_on_def by auto
      then have "card (cvPD \<union> {{x,y}}) = (card ?minPD) + 1" using cvPD_def(2) card_def
          by (simp add: \<open>\<Union> cvPD = PD\<close> finite_PD finite_UnionD)
      then have "card cvf = (card ?minPD) + 1" using cvf_def by auto
      then have "card cvf = card lac" using card_minPD
        by (metis Diff_infinite_finite Suc_eq_plus1 
            \<open>lac = {x. is_minimal_in_set P x}\<close> \<open>{x, y} \<subseteq> P\<close> 
            card_Diff_singleton card_Suc_Diff1 finite_PD finite_subset 
            less.prems(2) minPD_sub x)
         then show ?thesis using cv_cvf by blast
    qed
  qed
qed

section "Dilworth's Theorem for Chain Covers: Statement and Proof"

text \<open> We show that in any partially ordered set, the cardinality of 
a largest antichain is equal to the cardinality of a smallest chain cover.\<close>

theorem Dilworth: 
  assumes "largest_antichain_on P lac" 
      and "finite P" 
  shows "\<exists> cv. (smallest_chain_cover_on P cv) \<and> (card cv = card lac)"
proof-
  show ?thesis 
    using antichain_card_leq largest_antichard_card_eq assms largest_antichain_on_def
    by (smt (verit, ccfv_SIG) card.empty chain_cover_null le_antisym le_zero_eq 
            smallest_chain_cover_on_def)
qed


section "Dilworth's Decomposition Theorem"

subsection "Preliminaries"

text  \<open>Now we will strengthen the result above to prove that the cardinality of a 
smallest chain decomposition is equal to the cardinality of a largest antichain. 
In order to prove that, we construct a preliminary result which states that 
cardinality of smallest chain decomposition is equal to the cardinality of smallest 
chain cover.\<close>

text  \<open>We begin by constructing the function make\_disjoint which takes a list of sets 
and returns a list of sets which are mutually disjoint, and leaves the union of the 
sets in the list invariant. This function when acting on a chain cover returns a 
chain decomposition.\<close>

fun make_disjoint::"_ set list \<Rightarrow> _ "
  where
 "make_disjoint [] = ([])"
|"make_disjoint (s#ls) = (s - (\<Union> (set ls)))#(make_disjoint ls)"


lemma finite_dist_card_list:
  assumes "finite S"
  shows "\<exists>ls. set ls = S \<and> length ls = card S \<and> distinct ls"
  using assms  distinct_card finite_distinct_list
  by metis

lemma len_make_disjoint:"length xs = length (make_disjoint xs)"
  by (induction xs, simp+)

text  \<open>We use the predicate @{term "list_all2 (\<subseteq>)"}, which checks if two lists (of sets) 
have equal length, and if each element in the first list is a subset of the 
corresponding element in the second list.\<close>

lemma subset_make_disjoint: "list_all2 (\<subseteq>) (make_disjoint xs) xs"
  by (induction xs, simp, auto)

lemma subslist_union:
 assumes "list_all2 (\<subseteq>) xs ys"
 shows "\<Union> (set xs) \<subseteq> \<Union> (set ys)"
  using assms by(induction, simp, auto)

lemma make_disjoint_union:"\<Union> (set xs) = \<Union> (set (make_disjoint xs))"
proof
  show "\<Union> (set xs) \<subseteq> \<Union> (set (make_disjoint xs))"
    by (induction xs, auto) 
next
  show "\<Union> (set (make_disjoint xs)) \<subseteq> \<Union> (set xs)"
    using subslist_union subset_make_disjoint
    by (metis) 
qed

lemma make_disjoint_empty_int:
  assumes "X \<in> set (make_disjoint xs)" "Y \<in> set (make_disjoint xs)"
 and "X \<noteq> Y"
shows "X \<inter> Y = {}"
  using assms
proof(induction xs arbitrary: X Y)
  case (Cons a xs)
  then show ?case
  proof(cases "X \<noteq> a - (\<Union> (set xs)) \<and> Y \<noteq> (a - (\<Union> (set xs)))")
    case True
    then show ?thesis using Cons(1)[of X Y] Cons(2,3) 
      by (smt (verit, del_insts) Cons.prems(3) Diff_Int_distrib Diff_disjoint 
          Sup_upper make_disjoint.simps(2) make_disjoint_union inf.idem inf_absorb1 
          inf_commute set_ConsD) 
  next
    case False
    hence fa:"X = a -  (\<Union> (set xs))  \<or> Y = a -  (\<Union> (set xs)) " by argo
    then show ?thesis 
    proof(cases "X = a -  (\<Union> (set xs)) ")
      case True
      hence "Y \<noteq> a -  (\<Union> (set xs)) " using Cons(4) by argo
      hence "Y \<in> set (make_disjoint xs)" using Cons(3) by simp
      hence "Y \<subseteq> \<Union> (set (make_disjoint xs))" by blast
      hence "Y \<subseteq> \<Union> (set xs)" using make_disjoint_union by metis
      hence "X \<inter> Y = {}" using True by blast
      then show ?thesis by blast
    next
      case False
      hence Y:"Y = a -  (\<Union> (set xs))" using Cons(4) fa by argo
      hence "X \<noteq> a -  (\<Union> (set xs))" using False by argo
      hence "X \<in> set (make_disjoint xs)" using Cons(2) by simp
      hence "X \<subseteq> \<Union> (set (make_disjoint xs))" by blast
      hence "X \<subseteq> \<Union> (set xs)" using make_disjoint_union by metis
      hence "X \<inter> Y = {}" using Y by blast
      then show ?thesis by blast
    qed
  qed
qed (simp)

lemma chain_subslist:
  assumes "\<forall>i < length xs. Complete_Partial_Order.chain (\<le>) (xs!i)"
    and "list_all2 (\<subseteq>) ys xs"
  shows "\<forall>i < length ys. Complete_Partial_Order.chain (\<le>) (ys!i)"
  using assms(2,1)
proof(induction)
  case (Cons x xs y ys)
  then have "list_all2 (\<subseteq>) xs ys"  by auto
  then have le:" \<forall>i<length xs. Complete_Partial_Order.chain (\<le>) (xs ! i)" 
    using Cons by fastforce
  then have "x \<subseteq> y" using Cons(1) by auto
  then have "Complete_Partial_Order.chain (\<le>) x" using Cons 
    using chain_subset by fastforce
  then show ?case using le 
    by (metis all_nth_imp_all_set insert_iff list.simps(15) nth_mem) 
qed(argo)

lemma chain_cover_disjoint:
  assumes "chain_cover_on P (set C)"
  shows "chain_cover_on P (set (make_disjoint C))"
proof-
  have "\<Union> (set (make_disjoint C)) = P" using make_disjoint_union assms(1) 
    unfolding chain_cover_on_def by metis
  moreover have "\<forall>x\<in>set (make_disjoint C). x \<subseteq> P"
    using subset_make_disjoint assms unfolding chain_cover_on_def 
    using calculation by blast
  moreover have "\<forall>x\<in>set (make_disjoint C). Complete_Partial_Order.chain (\<le>) x" 
    using chain_subslist assms unfolding chain_cover_on_def chain_on_def 
    by (metis in_set_conv_nth subset_make_disjoint)
  ultimately show ?thesis   unfolding chain_cover_on_def chain_on_def by auto
qed

lemma make_disjoint_subset_i:
  assumes "i < length as"
  shows "(make_disjoint (as))!i \<subseteq> (as!i)" 
  using assms
proof(induct as arbitrary: i)
  case (Cons a as)
  then show ?case
  proof(cases "i = 0")
    case False
    have "i - 1 < length as" using Cons 
      using False by force
    hence "(make_disjoint as)! (i - 1) \<subseteq> as!(i - 1)" using Cons(1)[of "i - 1"]
      by argo
    then show ?thesis using False by simp
  qed (simp)
qed (simp)

text  \<open>Following theorem asserts that the corresponding to the smallest chain cover on 
a finite set, there exists a corresponding chain decomposition of the same cardinality.\<close>

lemma chain_cover_decompsn_eq: 
  assumes "finite P"
      and "smallest_chain_cover_on P A"
    shows "\<exists> B. chain_decomposition P B \<and> card B = card A"
proof-
  obtain As where As:"set As = A" "length As = card A" "distinct As" 
    using assms
    by (metis chain_cover_on_def finite_UnionD finite_dist_card_list 
        smallest_chain_cover_on_def)
  hence ccdas:"chain_cover_on P (set (make_disjoint As))" 
    using assms(2) chain_cover_disjoint[of P As]
    unfolding smallest_chain_cover_on_def by argo
  hence 1:"chain_decomposition P (set (make_disjoint As))" 
    using make_disjoint_empty_int 
    unfolding chain_decomposition_def  by meson
  moreover have 2:"card (set (make_disjoint As)) = card A"
  proof(rule ccontr)
    assume asm:"\<not> card (set (make_disjoint As)) = card A"
    have "length (make_disjoint As) = card A" 
      using len_make_disjoint As(2) by metis
    then show False 
      using asm assms(2) card_length ccdas 
            smallest_chain_cover_on_def 
      by metis
  qed
  ultimately show ?thesis by blast
qed
  
  
lemma smallest_cv_cd:
  assumes "smallest_chain_decomposition P cd"
        and "smallest_chain_cover_on P cv"
      shows "card cv \<le> card cd"
  using assms unfolding smallest_chain_decomposition_def chain_decomposition_def
       smallest_chain_cover_on_def by auto

lemma smallest_cv_eq_smallest_cd:
  assumes "finite P"
         and "smallest_chain_decomposition P cd"
        and "smallest_chain_cover_on P cv"
      shows "card cv = card cd"
  using smallest_cv_cd[OF assms(2,3)] chain_cover_decompsn_eq[OF assms(1,3)]
  by (metis assms(2) smallest_chain_decomposition_def)


subsection "Statement and Proof "

text\<open>We extend the Dilworth's theorem to chain decomposition. The following theorem 
asserts that size of a largest antichain is equal to the size of a smallest chain 
decomposition.\<close>

theorem Dilworth_Decomposition: 
  assumes "largest_antichain_on P lac" 
      and "finite P" 
    shows "\<exists> cd. (smallest_chain_decomposition P cd) \<and> (card cd = card lac)"
  using Dilworth[OF assms] smallest_cv_eq_smallest_cd assms 
  by (metis (mono_tags, lifting) cd_cv chain_cover_decompsn_eq 
       smallest_chain_cover_on_def  smallest_chain_decomposition_def) 
 
end 
(*ends the context*)
end