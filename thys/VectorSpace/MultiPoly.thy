theory MultiPoly

imports 
  Main 
  "~~/src/HOL/Algebra/Group"
  "~~/src/HOL/Algebra/Ring"
  "~~/src/HOL/Algebra/UnivPoly"
  "~~/src/HOL/Number_Theory/Binomial"
  Vectors
  LinearCombinations
begin

declare Let_def [[simp]]

(*record 'a pointed =  "'a partial_object" +
  point    :: "'a"

locale pointed_set =
  fixes G (structure) 
  assumes point_in_set: "point \<in> carrier G"

sublocale monoid \<subseteq> pointed_set

locale monoid =
  fixes G (structure)
  assumes m_closed [intro, simp]:
         "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> carrier G"*)

definition finitely_many_nonzero:: "('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> bool" where
  "finitely_many_nonzero f pt = finite {a. f a \<noteq> pt}"
definition finitely_many_nonzero_set:: "  'b \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "finitely_many_nonzero_set pt = {f. finite {a. f a \<noteq> pt}}"

definition zero_outside:: "('a\<Rightarrow>'b) \<Rightarrow>  'a set \<Rightarrow> 'b \<Rightarrow> bool" where
  "zero_outside f A pt = (\<forall>a\<in>-A. f a = pt)" 
definition zero_outside_set:: " 'a set  \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "zero_outside_set A pt = {f. (\<forall>a\<in>-A. f a = pt)}" 

(*definition nonzero_only_in:: "('a\<Rightarrow>'b) \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool" where
  "nonzero_only_in f A pt = (\<forall>a\<in>-A. f a = pt)" 
definition nonzero_only_in_set:: " 'a set \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "nonzero_only_in_set A pt = {f. (\<forall>a\<in>-A. f a = pt)}"*)

lemma finitely_many_equiv:
  fixes A B pt
  assumes "(\<Union>i::nat. A i) = B" "\<And>i j. i<j \<Longrightarrow>A i \<subseteq> A j"
  shows "(zero_outside f B pt) \<and> (finitely_many_nonzero f pt)
    = (\<exists>i. zero_outside f (A i) pt)"
sorry
(*lemma (in module) nested_union_vs: 
  fixes I N N'
  assumes subm: "\<And>i. i\<in>I\<Longrightarrow> submodule R (N i) M"
    and max_exists: "\<And>i j. i\<in>I\<Longrightarrow>j\<in>I\<Longrightarrow> (\<exists>k. k\<in>I \<and> N i\<subseteq>N k \<and> N j \<subseteq>N k)" 
    and uni: "N'=(\<Union> i\<in>I. N i)"
    and ne: "I\<noteq>{}"
  shows "submodule R N' M"*)

(*
instantiation list::zero 
begin
  definition plus ::"int list \<Rightarrow> int list \<Rightarrow> int list" where
    plus f g = map (\<lambda>(x,y). x + y) zip f g 
end*)

(*list to func and func to list*)



abbreviation one_poly:: "nat \<Rightarrow> int" where
  "one_poly n \<equiv> (if n=0 then 1 else 0)"

(*typedef 'a fs_map = "UNIV:: ((nat \<Rightarrow> int) \<Rightarrow> 'a) set"
..*)



text {* terms with at most n variables *}
abbreviation lt_n_vars:: "nat \<Rightarrow> (nat\<Rightarrow> int) set" where
  "lt_n_vars n \<equiv> zero_outside_set {..<n} 0"

text {* terms with positive exponents *}
abbreviation pos_exps:: "(nat\<Rightarrow> int) set" where
  "pos_exps \<equiv> {v. \<forall>i. v i \<ge>0}"

text {* terms with degree $\le d$ in first $n$ variables*}
abbreviation deg_lt:: "nat \<Rightarrow> int \<Rightarrow> (nat\<Rightarrow> int) set" where
  "deg_lt n d\<equiv> {v. (\<Sum>i\<le>n. v i) \<le> d} " 

(*
abbreviation bool_func_to_set:: "('a\<Rightarrow>bool) \<Rightarrow>('a set)" where
  "bool_func_to_set p \<equiv> {x. px}"*)

(*
abbreviation (in ring) all_in:: "('b\<Rightarrow>'a) \<Rightarrow>bool" where
  "all_in f \<equiv> (\<forall> x. f x \<in> carrier R)"*)

(*can't do 'b\<Rightarrow>*)

abbreviation (in ring) all_in_carrier:: "((nat \<Rightarrow> int)\<Rightarrow>'a) set" where
  "all_in_carrier \<equiv> {f. (\<forall> x. f x \<in> carrier R)}"

abbreviation (in ring) inf_Laurent_set:: "nat \<Rightarrow> ((nat \<Rightarrow> int) \<Rightarrow> 'a) set" where
  "inf_Laurent_set n \<equiv>  all_in_carrier \<inter> zero_outside_set (lt_n_vars n) \<zero>\<^bsub>R\<^esub>"

abbreviation (in ring) fs_set:: "nat \<Rightarrow> ((nat \<Rightarrow> int) \<Rightarrow> 'a) set" where
  "fs_set n \<equiv> all_in_carrier \<inter> zero_outside_set (lt_n_vars n \<inter> pos_exps) \<zero>\<^bsub>R\<^esub>"

abbreviation (in ring) poly_set:: "nat \<Rightarrow> ((nat \<Rightarrow> int) \<Rightarrow> 'a) set" where
  "poly_set n \<equiv> all_in_carrier \<inter> (zero_outside_set (lt_n_vars n \<inter> pos_exps) \<zero>\<^bsub>R\<^esub>) \<inter> 
    (finitely_many_nonzero_set \<zero>\<^bsub>R\<^esub>)"

abbreviation (in ring) large_fs:: "('a,((nat \<Rightarrow> int) \<Rightarrow> 'a)) module"
  where "large_fs \<equiv> func_space UNIV"

abbreviation (in ring) fs_module:: "nat \<Rightarrow> ('a,((nat \<Rightarrow> int) \<Rightarrow> 'a)) module"
  where "fs_module n \<equiv> LinearCombinations.module.md large_fs (fs_set n)"

abbreviation (in ring) poly_module:: "nat \<Rightarrow> ('a,((nat \<Rightarrow> int) \<Rightarrow> 'a)) module"
  where "poly_module n \<equiv> LinearCombinations.module.md large_fs (poly_set n)"

abbreviation iv ::"nat \<Rightarrow> (nat \<Rightarrow> int) ring" where
  "iv n \<equiv> \<lparr>carrier = lt_n_vars n, 
                          mult = (\<lambda>f g. \<lambda>v. 0),
                          one = (\<lambda>v. 0),
                          zero = (\<lambda>v. 0),
                          add = (\<lambda>f g. \<lambda>v. f v + g v)
                          \<rparr>"

lemma int_vectors_abelian_group: 
  "abelian_group (iv n)"
    apply (unfold_locales)
    apply (unfold zero_outside_set_def, auto)
    apply (rename_tac f)
    apply (unfold Units_def)
    apply simp
    by (rule_tac x=" (\<lambda>y. -f y)" in exI, auto)

(*lemma (in cring) large_fs_is_module [simp]: 
  "module R (large_fs)"
by (rule func_space_is_module)*)

(*declare cring.func_space_is_module [[simp]]*)

lemma (in module) submodule_is_module':
  fixes N::"'c set"
  assumes 0: "module R M \<Longrightarrow>submodule R N M"
  shows "module R (md N)"
proof -
  have 1: "module R M"..
  from assms 1 show ?thesis
    by (intro submodule_is_module, auto)
qed

lemma (in cring) fs_is_module[simp]: 
  "module R (fs_module n)"
  apply (intro module.submodule_is_module')
  apply (rule func_space_is_module)
  by (unfold zero_outside_set_def submodule_def func_space_def, auto)

lemma (in cring) poly_is_module[simp]: 
  "module R (poly_module n)"
proof - 
  have 1:
    "\<And>v w. \<forall>x. v x \<in> carrier R \<Longrightarrow>
           \<forall>x. w x \<in> carrier R \<Longrightarrow>
           {a. v a \<oplus> w a \<noteq> \<zero>} \<subseteq> {a. v a \<noteq> \<zero>} \<union> {a. w a \<noteq> \<zero>}"
  by auto
  have 2:
    "\<And>c v. c\<in> carrier R \<Longrightarrow> \<forall>x. v x \<in> carrier R  \<Longrightarrow>
           {a. c \<otimes> v a \<noteq> \<zero>} \<subseteq> {a. v a \<noteq> \<zero>}"
  by auto
  show ?thesis
    apply (intro module.submodule_is_module')
    apply (rule func_space_is_module)
    apply (unfold zero_outside_set_def finitely_many_nonzero_set_def 
        submodule_def func_space_def, auto)
    apply (drule 1, auto, smt2 finite_Un finite_subset)
    by (drule 2, auto, smt2 finite_subset)  

text {* update function space with multiplication and one. *}
definition (in ring) fs_algebra:: "nat \<Rightarrow> ('a,((nat \<Rightarrow> int) \<Rightarrow> 'a)) module" where
  "fs_algebra n = (let A = pos_exps \<inter> lt_n_vars n in 
    (fs_module n)
    \<lparr>mult := (\<lambda> f g. (\<lambda> v. if v\<in>A then 
            (\<Oplus>\<^bsub>R\<^esub> pr\<in> {pr\<in>A \<times> A. (fst pr) \<oplus>\<^bsub>iv n\<^esub> (snd pr)= v}. 
              f (fst pr) \<otimes>\<^bsub>R\<^esub> g (snd pr)) else \<zero>\<^bsub>R\<^esub>)),
     one := (\<lambda>v. (if (v = one_poly) then \<one>\<^bsub>R\<^esub> else \<zero>\<^bsub>R\<^esub>))\<rparr>)"

lemma module_criteria2:
  fixes R and M 
  assumes "module R M"
  shows "cring R 
      \<and> \<zero>\<^bsub>M\<^esub>\<in> carrier M
      \<and> (\<forall>v w. v\<in>carrier M \<and> w\<in>carrier M\<longrightarrow> v\<oplus>\<^bsub>M\<^esub> w\<in> carrier M)
      \<and> (\<forall>v\<in>carrier M. (\<exists>neg_v\<in>carrier M. v\<oplus>\<^bsub>M\<^esub>neg_v=\<zero>\<^bsub>M\<^esub>))
      \<and> (\<forall>c v. c\<in> carrier R \<and> v\<in>carrier M\<longrightarrow> c\<odot>\<^bsub>M\<^esub> v \<in> carrier M)
      \<and> (\<forall>v w. v\<in>carrier M \<and> w\<in>carrier M\<longrightarrow> v\<oplus>\<^bsub>M\<^esub> w=w\<oplus>\<^bsub>M\<^esub> v)
      \<and> (\<forall>v w x. v\<in>carrier M \<and> w\<in>carrier M \<and> x\<in>carrier M\<longrightarrow> (v\<oplus>\<^bsub>M\<^esub> w)\<oplus>\<^bsub>M\<^esub> x= v\<oplus>\<^bsub>M\<^esub> (w\<oplus>\<^bsub>M\<^esub> x))
      \<and> (\<forall>v\<in>carrier M. (v\<oplus>\<^bsub>M\<^esub> \<zero>\<^bsub>M\<^esub> =v))
      \<and> (\<forall>a b v. a\<in> carrier R \<and> b\<in> carrier R \<and> v\<in>carrier M\<longrightarrow> (a\<otimes>\<^bsub>R\<^esub> b)\<odot>\<^bsub>M\<^esub> v =a\<odot>\<^bsub>M\<^esub> (b\<odot>\<^bsub>M\<^esub> v))
      \<and> (\<forall>v\<in>carrier M. (\<one>\<^bsub>R\<^esub> \<odot>\<^bsub>M\<^esub> v =v))
      \<and> (\<forall>a b v. a\<in> carrier R \<and> b\<in> carrier R \<and> v\<in>carrier M\<longrightarrow> (a\<oplus>\<^bsub>R\<^esub> b)\<odot>\<^bsub>M\<^esub> v =(a\<odot>\<^bsub>M\<^esub> v) \<oplus>\<^bsub>M\<^esub> (b\<odot>\<^bsub>M\<^esub> v))
      \<and> (\<forall>a v w. a\<in> carrier R \<and> v\<in>carrier M \<and> w\<in>carrier M\<longrightarrow> a\<odot>\<^bsub>M\<^esub> (v\<oplus>\<^bsub>M\<^esub> w) =(a\<odot>\<^bsub>M\<^esub> v) \<oplus>\<^bsub>M\<^esub> (a\<odot>\<^bsub>M\<^esub> w))"
proof -
  from assms interpret M: module R M by auto
  from assms show ?thesis
    apply (auto simp add: M.a_ac M.smult_assoc1 M.smult_l_distr M.smult_r_distr)
    by (unfold module_def, auto)
qed

lemma module_no_mult[simp]: "module R M \<Longrightarrow> module R (M\<lparr>mult:= m, one:= on\<rparr>)"
proof -
  assume "module R M"
  thus ?thesis 
    apply (subst refl)
    apply (drule module_criteria2)
    apply (intro module_criteria)
    by auto
qed



lemma (in cring) fsa_is_module[simp]: 
  "module R (fs_algebra n)"
proof - 
  have fsm: "module R (fs_module n)" by (rule fs_is_module)
  from fsm show ?thesis 
    by (unfold fs_algebra_def,simp add: Let_def)
qed


(*A = Avectors {m. m\<ge>0} n*)
(*"inverses A B f g \<equiv> (f\<in>A\<rightarrow>B)\<and>(g\<in>B\<rightarrow>A)\<and> (\<forall> a\<in>A. g (f a) = a) \<and> (\<forall>b\<in>B. f (g b) = b)"
*)
(* [simp]*)
lemma subset_carrier:
  assumes "a\<in>B" "B\<subseteq>carrier G"
  shows "a\<in>carrier G"
proof - 
  from assms show ?thesis by auto
qed

lemma rewrite_tuple1: 
  assumes A: "A= pos_exps \<inter> lt_n_vars n"
  shows "inverses 
          {((a,w),(b,c))\<in>(A\<times>A)\<times>(A\<times>A). a\<oplus>\<^bsub>iv n\<^esub>w=v \<and> b\<oplus>\<^bsub>iv n\<^esub>c=w}
          {(a,b,c)\<in>(A\<times>A\<times>A). a\<oplus>\<^bsub>iv n\<^esub>b\<oplus>\<^bsub>iv n\<^esub>c=v}
          (\<lambda> ((a,w), (b,c)). (a,b,c))
          (\<lambda> (a,b,c). ((a,b\<oplus>\<^bsub>iv n\<^esub>c), (b,c)))"
proof - 
  interpret iv: abelian_group "iv n" by (rule int_vectors_abelian_group)
  from A have sub: " A \<subseteq> carrier (iv n)" 
    by auto
  from A sub show ?thesis
    apply (auto simp add: iv.a_ac subset_carrier)
    by (unfold zero_outside_set_def, auto)
qed

locale FSA = R: cring R 
    for R (structure) +
  fixes n RX
  assumes RX[simp]: "RX = fs_algebra n"

(* HOL.ext*)
(*lemma func_ext: "(\<And>x. f x = g x) \<Longrightarrow> f = g"
  by auto*)
(*lemma carrier_simp1: "ring R \<Longrightarrow> carrier (ring.func_space R S) = S"*)


lemma (in cring) finsum_distr_l:
  "[| finite A; c\<in> carrier R; f \<in> A -> carrier R |] ==>
   (finsum R f A \<otimes>\<^bsub>R\<^esub> c) = finsum R (%x. f x \<otimes>\<^bsub>R\<^esub> c) A "
proof (induct set: finite)
  case empty 
  from `c\<in>carrier R` show ?case 
    by simp
next
  case (insert a A)
  from insert.hyps insert.prems have 1: "finsum R f (insert a A) = f a \<oplus>\<^bsub>R\<^esub> finsum R f A"
    by (intro finsum_insert, auto)
  from insert.hyps insert.prems have 2: "(\<Oplus>\<^bsub>R\<^esub>x\<in>insert a A. f x \<otimes>\<^bsub>R\<^esub> c) = f a \<otimes>\<^bsub>R\<^esub> c \<oplus>\<^bsub>R\<^esub>(\<Oplus>\<^bsub>R\<^esub>x\<in>A. f x \<otimes>\<^bsub>R\<^esub> c)" 
    by (intro finsum_insert, auto)
  from insert.hyps insert.prems show ?case 
    by (auto simp add:1 2 l_distr finsum_closed)
qed

lemma (in cring) finsum_distr_r:
  assumes "finite A" "c\<in> carrier R" "f \<in> A -> carrier R"
  shows " (c \<otimes>\<^bsub>R\<^esub>  finsum R f A ) = finsum R (%x. c \<otimes>\<^bsub>R\<^esub> f x) A "
proof -
  from assms have l: "(finsum R f A \<otimes>\<^bsub>R\<^esub> c) = finsum R (%x. f x \<otimes>\<^bsub>R\<^esub> c) A" 
    by (rule finsum_distr_l)
  from assms l show ?thesis
    apply (subst refl)
    apply (drule Pi_implies_Pi2)
    by (simp add: m_ac a_ac Pi_simp subset_carrier cong: finsum_cong)
qed

lemma (in comm_monoid) finprod_cong2':
  "[| A = B; 
      !!i. i \<in> B =simp=> f i = g i ; g \<in> B -> carrier G|] ==> finprod G f A = finprod G g B"
 apply (auto cong: finprod_cong)
sorry

lemmas (in abelian_monoid) finsum_cong2' = add.finprod_cong2'

lemma (in comm_monoid) finprod_cong3':
  "[| A = B; 
      !!i. i \<in> B ==> f i = g i ; f \<in> B -> carrier G|] ==> finprod G f A = finprod G g B"
 apply (auto cong: finprod_cong')
done

lemmas (in abelian_monoid) finsum_cong3' = add.finprod_cong3'

lemma simp_if:
  "\<And>x. ((\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> P x \<Longrightarrow> ((if (Q x) then (f x) else (g x)) = f x))"
apply simp
done


lemma (in comm_monoid) finprod_elim_if:
  assumes "finite A" "\<And> x. x\<in>A\<Longrightarrow>P x" "f \<in> A -> carrier G"
  shows " finprod G (\<lambda>x. if P x then f x else g x) A  = finprod G f A"
proof -
  from assms show ?thesis 
    apply (simp cong: finprod_cong')
done
qed

lemma (in comm_monoid) finprod_exp:
  assumes 1: "A={x. P x \<and> Q x}" and 2:"finite A" and 3: "a\<in>A\<rightarrow>carrier G"
  shows "finprod G (\<lambda>x. if P x then 
    a x else b x) A = finprod G a A"
proof - 
  from 1 3 have 4: "(\<lambda>x. if P x then 
    a x else b x) \<in> A\<rightarrow>carrier G" apply auto done
  from assms show ?thesis
(*[THEN [3] 4]*)
using[[simp_trace, simp_trace_depth_limit=10]]
apply (auto cong: finprod_cong2' simp add:simp_if  split:if_splits del: Pi_I')
apply (intro finprod_cong2')
apply simp
apply simp
apply simp
sorry

context FSA
begin

(*lemma finite_PiE: "finite S \<Longrightarrow> (\<And>i. i \<in> S \<Longrightarrow> finite (T i)) \<Longrightarrow> finite (PIE i : S. T i)"
  by (induct S arbitrary: T rule: finite_induct) (simp_all add: PiE_insert_eq)
*)

(*If a function takes finitely many values in a given set, and is 0 outside
the set, there are finitely many possibilities for the function.*)
lemma finite_poss:
  assumes A_fin: "finite A" and zero:"\<And>f. f\<in>C \<Longrightarrow> zero_outside f A pt" and 
    poss: "\<And>f i. f\<in>C \<Longrightarrow> i\<in>A \<Longrightarrow> f i \<in> B i" and B: "\<And>i. i\<in>A \<Longrightarrow> finite (B i)"
  shows "finite C"
proof -
  let ?D="{f. zero_outside f A pt \<and> (\<forall>i. i\<in>A \<longrightarrow> f i \<in> B i)}"
  have inv: "inverses ?D (PiE A B) (\<lambda>f. (\<lambda> i. if i\<in>A then f i else undefined))
    (\<lambda>f. (\<lambda> i. if i\<in>A then f i else pt))" (is "inverses ?D ?E ?g ?h")
    apply (unfold zero_outside_def PiE_def extensional_def)
    by (auto)
  from A_fin B have Pie: "finite (PiE A B)" by (intro finite_PiE, auto)
  from inv Pie have D: "finite ?D" 
    apply (intro bijection_card_eq(1)[where ?A="?D"
      and ?B="?E" and ?f="?g" and ?g="?h"])
    by auto
  from zero poss have sub: "C\<subseteq>?D" by auto
  from sub D show ?thesis by (simp add: rev_finite_subset)
qed

(*helper lemma, show finiteness*)
lemma assoc_helper1: 
  assumes A: "A= pos_exps \<inter> lt_n_vars n" and v: "v\<in>A"
  shows "finite {pr\<in>A \<times> A. (fst pr) \<oplus>\<^bsub>iv n\<^esub> (snd pr)= v}" (is "finite ?S")
proof - 
  from v A have "\<And>i. i\<le>n \<Longrightarrow> v i \<ge>0" by auto
  {
    fix par i
    assume AxA: "par\<in>A \<times> A" and sum: "(fst par) \<oplus>\<^bsub>iv n\<^esub> (snd par)= v"
    from sum have sumi: "(fst par) i + (snd par) i = v i" by auto
    from A AxA sumi have 1: "(fst par) i \<ge>0 \<and> (fst par) i \<le>v i\<and>(snd par) i \<ge>0 \<and> (snd par) i \<le>v i" apply auto
      apply (metis le_add_same_cancel1)
      by (metis le_add_same_cancel2)
  }
  from this A v have f1: "finite (fst`{pr\<in>A \<times> A. (fst pr) \<oplus>\<^bsub>iv n\<^esub> (snd pr)= v})" 
      apply (intro finite_poss[where ?C="fst `{pr\<in>A \<times> A. (fst pr) \<oplus>\<^bsub>iv n\<^esub> (snd pr)= v}" 
          and ?A="{..<n}" and ?pt=0
          and ?B="\<lambda>i. {0.. v i}"])
      by (auto simp add: zero_outside_set_def zero_outside_def)
  from this A v have f2: "finite (snd`{pr\<in>A \<times> A. (fst pr) \<oplus>\<^bsub>iv n\<^esub> (snd pr)= v})" 
      apply (intro finite_poss[where ?C="snd `{pr\<in>A \<times> A. (fst pr) \<oplus>\<^bsub>iv n\<^esub> (snd pr)= v}" 
          and ?A="{..<n}" and ?pt=0
          and ?B="\<lambda>i. {0.. v i}"])
      by (auto simp add: zero_outside_set_def zero_outside_def)   
  have f3: "?S \<subseteq> (fst`?S \<times> snd `?S)" apply (unfold image_def, auto)
    by blast
(*sledge fails given just f1 f2.*)
  from f1 f2 f3 show ?thesis 
    by (intro finite_subset[where ?A="?S" and ?B="(fst`?S \<times> snd `?S)"], auto)
qed

lemma split_prod:
  "(p\<in>A \<times> B) = (fst p \<in>A \<and> snd p \<in>B)"
by (metis mem_Sigma_iff prod.collapse)


lemma in_c:
  "\<forall>x\<in>A. f x \<in>carrier R \<Longrightarrow> f\<in>A\<rightarrow>carrier R"
apply simp
done



lemma fs_mult_assoc:
  assumes p: "p \<in> carrier RX"
    and q: "q \<in> carrier RX"
    and r: "r \<in> carrier RX"
  shows "(p\<otimes>\<^bsub>RX\<^esub>q) \<otimes>\<^bsub>RX\<^esub>r = p\<otimes>\<^bsub>RX\<^esub> (q \<otimes>\<^bsub>RX\<^esub>r)"
proof-
  interpret iv: abelian_group "iv n" by (rule int_vectors_abelian_group)
  let ?A="pos_exps \<inter> lt_n_vars n"
  have "?A \<subseteq> carrier (iv n)" by auto
  interpret fsa: module R "(fs_algebra n)" by (rule fsa_is_module)
  (*from assoc_helper1 have " \<And>v. \<forall>x. p x \<in> carrier R \<Longrightarrow>
    p \<in> zero_outside_set (lt_n_vars n \<inter> {v. \<forall>i. 0 \<le> v i}) \<zero> \<Longrightarrow>
    \<forall>x. q x \<in> carrier R \<Longrightarrow>
    q \<in> zero_outside_set (lt_n_vars n \<inter> {v. \<forall>i. 0 \<le> v i}) \<zero> \<Longrightarrow>
    \<forall>x. r x \<in> carrier R \<Longrightarrow>
    r \<in> zero_outside_set (lt_n_vars n \<inter> {v. \<forall>i. 0 \<le> v i}) \<zero> \<Longrightarrow>
     (\<Oplus>pr\<in>{pr \<in>
                ({v. \<forall>i. 0 \<le> v i} \<inter> lt_n_vars n) \<times>
                ({v. \<forall>i. 0 \<le> v i} \<inter> lt_n_vars n).
                (\<lambda>v. fst pr v + snd pr v) =
                v}. (\<Oplus>pr\<in>{pra \<in>
                            ({v. \<forall>i. 0 \<le> v i} \<inter> lt_n_vars n) \<times>
                            ({v. \<forall>i. 0 \<le> v i} \<inter> lt_n_vars n).
                            (\<lambda>v. fst pra v + snd pra v) =
                            fst pr}. p (fst pr) \<otimes> q (snd pr)) \<otimes>
                    r (snd pr)) \<in>carrier R"
                    apply (intro finsum_closed)
defer
apply auto

try0
                        apply (auto cong: fsa.finsum_cong2 
      simp add: fsa.a_ac subset_carrier finsum_distr_l finsum_distr_r 
      split: prod.split)*)
  have trivial1: "\<And>pr v. pr \<in>{pr. (\<forall>i. 0 \<le> fst pr i) \<and>
                     fst pr \<in> lt_n_vars n \<and>
                     (\<forall>i. 0 \<le> snd pr i) \<and>
                     snd pr \<in> lt_n_vars n \<and>
                     (\<lambda>v. fst pr v + snd pr v) =
                     v} \<Longrightarrow> (\<forall>i. 0 \<le> fst pr i) \<and> fst pr \<in> lt_n_vars n" by simp
  from assoc_helper1 have 2: "\<And> pr p q v.   \<forall>x. p x \<in> carrier R \<Longrightarrow>   \<forall>x. q x \<in> carrier R \<Longrightarrow>pr\<in>{pr. pr \<in>
                 ({v. \<forall>i. 0 \<le> v i} \<inter> lt_n_vars n) \<times>
                 ({v. \<forall>i. 0 \<le> v i} \<inter> lt_n_vars n)} \<Longrightarrow> (if (\<forall>i. 0 \<le> fst pr i) \<and> fst pr \<in> lt_n_vars n
                          then \<Oplus>pr\<in>{pra \<in>
                                      ({v. \<forall>i. 0 \<le> v i} \<inter> lt_n_vars n) \<times>
                                      ({v. \<forall>i. 0 \<le> v i} \<inter> lt_n_vars n).
                                      fst pra \<oplus>\<^bsub>iv n\<^esub> snd pra =
                                      fst pr}. p (fst pr) \<otimes> q (snd pr)
                          else \<zero>) \<in>carrier R"
apply (
      simp add: fsa.a_ac Pi_simp subset_carrier finsum_distr_l finsum_distr_r split_prod
cong: fsa.finsum_cong2'       
split: prod.split)
 sorry


from assoc_helper1 have "\<And>v. (\<And>A v. A = {v. \<forall>i. 0 \<le> v i} \<inter> lt_n_vars n \<Longrightarrow>
                 (\<forall>i. 0 \<le> v i) \<and> v \<in> lt_n_vars n \<Longrightarrow>
                 finite
                  {pr. (\<forall>i. 0 \<le> fst pr i) \<and>
                       fst pr \<in> lt_n_vars n \<and>
                       (\<forall>i. 0 \<le> snd pr i) \<and>
                       snd pr \<in> lt_n_vars n \<and>
                       (\<lambda>v. fst pr v + snd pr v) = v}) \<Longrightarrow>
         (\<And>a b v.
             (\<forall>i. 0 \<le> a i) \<and>
             a \<in> lt_n_vars n \<and>
             (\<forall>i. 0 \<le> b i) \<and> b \<in> lt_n_vars n \<and> (\<lambda>v. a v + b v) = v \<Longrightarrow>
             True) \<Longrightarrow>
         (\<And>p q a b.
             \<forall>x. p x \<in> carrier R \<Longrightarrow>
             \<forall>x. q x \<in> carrier R \<Longrightarrow>
             (\<forall>i. 0 \<le> a i) \<and>
             a \<in> lt_n_vars n \<and> (\<forall>i. 0 \<le> b i) \<and> b \<in> lt_n_vars n \<Longrightarrow>
             True) \<Longrightarrow>
         \<forall>x. p x \<in> carrier R \<Longrightarrow>
         p \<in> zero_outside_set (lt_n_vars n \<inter> {v. \<forall>i. 0 \<le> v i}) \<zero> \<Longrightarrow>
         \<forall>x. q x \<in> carrier R \<Longrightarrow>
         q \<in> zero_outside_set (lt_n_vars n \<inter> {v. \<forall>i. 0 \<le> v i}) \<zero> \<Longrightarrow>
         \<forall>x. r x \<in> carrier R \<Longrightarrow>
         r \<in> zero_outside_set (lt_n_vars n \<inter> {v. \<forall>i. 0 \<le> v i}) \<zero> \<Longrightarrow>
         \<forall>i. 0 \<le> v i \<Longrightarrow>
         v \<in> lt_n_vars n \<Longrightarrow>
         (\<Oplus>pr\<in>{pr. (\<forall>i. 0 \<le> fst pr i) \<and>
                     fst pr \<in> lt_n_vars n \<and>
                     (\<forall>i. 0 \<le> snd pr i) \<and>
                     snd pr \<in> lt_n_vars n \<and>
                     (\<lambda>v. fst pr v + snd pr v) =
                     v}. (if (\<forall>i. 0 \<le> fst pr i) \<and> fst pr \<in> lt_n_vars n
                          then \<Oplus>pr\<in>{pra \<in>
                                      ({v. \<forall>i. 0 \<le> v i} \<inter> lt_n_vars n) \<times>
                                      ({v. \<forall>i. 0 \<le> v i} \<inter> lt_n_vars n).
                                      fst pra \<oplus>\<^bsub>iv n\<^esub> snd pra =
                                      fst pr}. p (fst pr) \<otimes> q (snd pr)
                          else \<zero>) \<otimes>
                         r (snd pr)) =
(\<Oplus>pr\<in>{pr. (\<forall>i. 0 \<le> fst pr i) \<and>
                     fst pr \<in> lt_n_vars n \<and>
                     (\<forall>i. 0 \<le> snd pr i) \<and>
                     snd pr \<in> lt_n_vars n \<and>
                     (\<lambda>v. fst pr v + snd pr v) =
                     v}. (\<Oplus>pr\<in>{pra \<in>
                                      ({v. \<forall>i. 0 \<le> v i} \<inter> lt_n_vars n) \<times>
                                      ({v. \<forall>i. 0 \<le> v i} \<inter> lt_n_vars n).
                                      fst pra \<oplus>\<^bsub>iv n\<^esub> snd pra =
                                      fst pr}. p (fst pr) \<otimes> q (snd pr)
                          ) \<otimes>
                         r (snd pr))"


apply (
      simp add: fsa.a_ac Pi_simp subset_carrier finsum_distr_l finsum_distr_r split_prod
cong: finsum_cong2'       
split: prod.split split_if)sorry

  from assoc_helper1 assms trivial1 2 show ?thesis
    apply simp
    apply (unfold fs_algebra_def, auto simp add: Let_def)
    apply (intro ext)
    apply (split split_if)
    apply auto
(*using [[simp_trace,simp_trace_depth_limit=10]]*)
    apply (
      simp add: fsa.a_ac Pi_simp subset_carrier finsum_distr_l finsum_distr_r split_prod
      cong: finsum_cong2'       
split: prod.split split_if)
(*fails*)
(*simp add: fsa.a_ac Pi_simp subset_carrier finsum_distr_l finsum_distr_r split_prod
cong: finsum_cong2'       
split: prod.split split_if*)
thm finsum_cong2
sorry
qed
end

lemma formal_series_is_algebra:
  assumes "cring R"
  shows "algebra R (fs_algebra R n)"
sorry


lemma poly_is_algebra:
  assumes "cring R"
  shows "algebra R (poly_algebra R n)"
sorry

(*
definition formal_series_module :: "'a ring \<Rightarrow> nat \<Rightarrow> 
  (('a, int list \<Rightarrow> 'a)  module)" where
  "formal_series_module R n = 
    (let A = Avectors {m. m\<ge>0} n in
      \<lparr>carrier = A \<rightarrow>\<^sub>E carrier R,
       mult = (\<lambda> f g. restrict (\<lambda> v. 
         \<Oplus>\<^bsub>R\<^esub> p\<in> {(x,y)\<in>A \<times> A. x\<oplus>\<^bsub>iv n\<^esub> y= v}. f (fst p) \<otimes>\<^bsub>R\<^esub> g (snd p)) A),
       one = restrict (\<lambda>v. (if v = one_list n then \<one>\<^bsub>R\<^esub> else \<zero>\<^bsub>R\<^esub>)) A,
       zero = restrict (\<lambda>v. \<zero>\<^bsub>R\<^esub>) A,
       add = (\<lambda> f g. restrict (\<lambda> v.  f v \<oplus>\<^bsub>R\<^esub> g v) A),
       smult = (\<lambda> c f. restrict (\<lambda> v.  c \<otimes>\<^bsub>R\<^esub> f v) A)\<rparr>)" 
*)

(*
\<lparr>carrier = {v. Atuple v (carrier K) n},
                  mult = (\<lambda> v w. []),
                  one = [],
                  zero = [\<zero>\<^bsub>K\<^esub>. x <- [0..<n]],
                  add = (\<lambda> v w. (map (\<lambda> (a,b). a \<oplus>\<^bsub>K\<^esub> b) (zip v w))),
                  smult = (\<lambda> c v. [c\<otimes>\<^bsub>K\<^esub> x. x<-v])
*)
end
