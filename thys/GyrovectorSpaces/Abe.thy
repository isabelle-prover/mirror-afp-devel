theory Abe
  imports GyroGroup "HOL-Analysis.Inner_Product" HOL.Real_Vector_Spaces VectorSpace
begin



locale one_dim_vector_space_with_domain =
  vector_space_with_domain + 
  assumes "\<forall>y. \<forall>x. (y\<in> dom \<and>
 x\<in> dom \<and> x\<noteq>zero \<longrightarrow> (\<exists>!r::real. y = smult r x))"
  
locale GGV = 
  fixes fi ::"'a::gyrocommutative_gyrogroup \<Rightarrow> 'b::real_inner"
  fixes scale ::"real \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes plus'::"real \<Rightarrow> real \<Rightarrow> real"
  fixes smult'::"real \<Rightarrow> real \<Rightarrow> real"
  (*fixes zero'::"real"*)
  assumes "inj fi"
  assumes "norm (fi (gyr u v a)) = norm (fi a)"
  assumes "scale 1 a = a"
  assumes "scale (r1+r2) a = (scale r1 a) \<oplus> (scale r2 a)"
  assumes "scale (r1*r2) a = scale r1 (scale r2 a)"
  assumes "(a\<noteq>gyrozero \<and> r\<noteq>0)\<longrightarrow> (fi (scale \<bar>r\<bar> a)) /\<^sub>R (norm (fi (scale r a))) = (fi a) /\<^sub>R (norm (fi a))"
  assumes "gyr u v (scale r a) = scale r (gyr u v a)"
  assumes "gyr (scale r1 v) (scale r2 v) = id"
  assumes "vector_space_with_domain {x.\<exists>a. x = norm (fi a) \<or> x = - norm (fi a)} plus' 0 smult'"
  assumes "norm (fi (scale r a)) = smult' \<bar>r\<bar> (norm (fi a))"
  assumes "norm (fi (a \<oplus> b)) = plus' (norm (fi a)) (norm (fi b))"
begin
  
end

class gyrolinear_space = 
  gyrocommutative_gyrogroup +
  fixes scale :: "real \<Rightarrow> 'a::gyrocommutative_gyrogroup  \<Rightarrow> 'a" (infixl "\<otimes>" 105) 
  assumes scale_1: "\<And> a :: 'a. 1 \<otimes> a = a"
  assumes scale_distrib: "\<And> (r1 :: real) (r2 :: real) (a :: 'a). (r1 + r2) \<otimes> a = r1 \<otimes> a \<oplus> r2 \<otimes> a"
  assumes scale_assoc: "\<And> (r1 :: real) (r2 :: real) (a :: 'a). (r1 * r2) \<otimes> a = r1 \<otimes> (r2 \<otimes> a)"
  assumes gyroauto_property: "\<And> (u :: 'a) (v :: 'a) (r :: real) (a :: 'a). gyr u v (r \<otimes> a) = r \<otimes> (gyr u v a)"
  assumes gyroauto_id: "\<And> (r1 :: real) (r2 :: real) (v :: 'a). gyr (r1 \<otimes> v) (r2 \<otimes> v) = id"
  
begin

end

locale normed_gyrolinear_space = 
  fixes norm'::"'a::gyrolinear_space \<Rightarrow> real"
  fixes f::"real \<Rightarrow> real"
  assumes "\<forall>a::'a. (norm' a \<ge> 0)"
  assumes "\<forall>y::real. (y\<in> (norm' ` UNIV) \<longrightarrow> (f y) \<ge> 0)"
  assumes "bij_betw f (norm' ` UNIV) {x::real. x\<ge>0}"
  assumes "\<forall>y::real. \<forall>z::real. (( y\<in> norm' ` UNIV \<and>
z\<in> norm' ` UNIV \<and> y>z)\<longrightarrow> (f y) > (f z))"

  assumes "\<forall>x::'a. \<forall>y::'a. f(norm' (gyroplus x y)) \<le> (f (norm' x)) + (f (norm' y))"
  assumes "f (norm' (scale r x)) = \<bar>r\<bar> * (f (norm' x))"
  assumes "norm' (gyr u v x) = norm' x"
  assumes "\<forall>x::'a. ((norm' x) = 0 \<longleftrightarrow> x = gyrozero)"
begin
  
definition norms::"real set" where 
  "norms = norm' ` UNIV"

definition norms_neg::"real set" where 
  "norms_neg = (\<lambda>x. -1 * norm' x) ` UNIV"

definition norms_all::"real set" where 
  "norms_all = norms \<union> norms_neg"

lemma norms_neq_not_empty:
  shows "norms_neg \<noteq> {}"
  using add.inverse_inverse norms_neg_def by fastforce


lemma zero_only_norms_norms_neg:
  assumes "x\<in>norms" "x\<in>norms_neg"
  shows "x=0"
  by (smt (verit, ccfv_threshold) assms(1) assms(2) f_inv_into_f normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_def norms_neg_def)


lemma a1_a2:
  shows "\<exists>f':: real \<Rightarrow> real. ((\<forall>x::real. \<forall>y::real. ( x\<in>norms_all \<and> y \<in>norms_all \<and> x>y)\<longrightarrow> (f' x) > (f' y))
 \<and> (f' 0) = 0 \<and> bij_betw f' norms_all UNIV)"  
proof-
  let ?f' = "\<lambda>x. if x=0 then 0 else if (x \<in> norms) then (f x) else if (x\<in> norms_neg) then - (f (-x)) else undefined" 
  have fact3: "?f' 0 = 0"
    by auto
  moreover have fact1: "(\<forall>x::real. \<forall>y::real. ( x\<in>norms_all \<and> y \<in>norms_all \<and> x>y)\<longrightarrow> (?f' x) > (?f' y))"
  proof-
    {fix x y 
    assume "x\<in>norms_all \<and> y \<in>norms_all \<and> x>y"
    have "(?f' x) > (?f' y)"
    proof-
      have "x=0 \<or> x\<noteq>0" by blast
      moreover {
        assume "x=0"
        then have ?thesis 
          by (smt (verit, del_insts) Un_def \<open>x \<in> norms_all \<and> y \<in> norms_all \<and> y < x\<close> f_inv_into_f mem_Collect_eq normed_gyrolinear_space.norms_neg_def normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_all_def norms_def rangeI)
          
      }
      moreover {
        assume "x\<noteq>0"
        have "x\<in>norms \<or> x\<in>norms_neg"
          using \<open>x \<in> norms_all \<and> y \<in> norms_all \<and> y < x\<close> norms_all_def by force
        moreover {
          assume "x\<in>norms"
          then have "y=0\<or> y\<noteq>0"
            by blast
          moreover {
            assume "y=0"
            then have ?thesis 
              by (smt (z3) \<open>x \<in> norms\<close> \<open>x \<in> norms_all \<and> y \<in> norms_all \<and> y < x\<close> normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_def rangeI)
          } moreover {
            assume "y\<noteq>0"
            have "y\<in>norms \<or> y\<in>norms_neg"
              using \<open>x \<in> norms_all \<and> y \<in> norms_all \<and> y < x\<close> norms_all_def by auto
            moreover {
              assume "y\<in>norms"
              then have ?thesis 
                by (smt (z3) \<open>x \<in> norms\<close> \<open>x \<in> norms_all \<and> y \<in> norms_all \<and> y < x\<close> \<open>x \<noteq> 0\<close> normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_def)
                
            } moreover {
              assume "y\<in>norms_neg"
              then have "?f' y = - (f (-y))"
                using \<open>y \<noteq> 0\<close> zero_only_norms_norms_neg by fastforce
              moreover have "-y \<in> norms"
                using \<open>y \<in> norms_neg\<close> norms_def norms_neg_def by force
              moreover have "?f' y \<le> 0"
     
                by (smt (verit, ccfv_threshold) calculation(1) calculation(2) normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_def)
                
              moreover have "?f' y \<noteq>0"
              proof(rule ccontr)
                assume "\<not>(?f' y \<noteq> 0)"
                then show False 
                  by (smt (verit, del_insts) \<open>y \<noteq> 0\<close> calculation(1) calculation(2) f_inv_into_f normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_def rangeI)
              qed
              ultimately have ?thesis 
                by (smt (z3) \<open>x \<in> norms\<close> normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_def) 
            }
            ultimately have ?thesis by blast
            }
            ultimately have ?thesis by blast
          } moreover {
            assume "x\<in>norms_neg"
            then have ?thesis 
              by (smt (verit, del_insts) Un_def \<open>x \<in> norms_all \<and> y \<in> norms_all \<and> y < x\<close> f_inv_into_f mem_Collect_eq normed_gyrolinear_space.norms_neg_def normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_all_def norms_def rangeI)

        }
        ultimately have ?thesis by blast
      } ultimately show ?thesis by blast
    qed
  }
  then show ?thesis by blast
qed
  moreover have fact2: " bij_betw ?f' norms_all UNIV"
  proof-
    have *:"\<forall>x. \<forall>y. (x\<in>norms_all \<and> y\<in>norms_all \<and> (?f' x) = (?f' y)) \<longrightarrow> x = y"
      by (smt (verit, ccfv_threshold) calculation(2))
    moreover have **:"\<forall>x::real. \<exists>y. (y\<in> norms_all \<and> ?f' y = x)"
    proof-
      have "\<forall>x::real. (x\<ge>0 \<longrightarrow> (\<exists>y. (y \<in> norms \<and> f y = x )))"
        by (metis (no_types, opaque_lifting) bij_betw_iff_bijections mem_Collect_eq normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_def)
      moreover have "\<forall>x::real. (x<0 \<longrightarrow> (\<exists>y. (y \<in> norms \<and> (f y) =  -x)))"
        by (simp add: calculation)
      moreover have  "\<forall>x::real. (x\<ge>0 \<longrightarrow> (\<exists>y. (y \<in> norms \<and> ?f' y = x )))"
        by (smt (z3) calculation(1) f_inv_into_f normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_def)
      moreover have  "\<forall>x::real. (x<0 \<longrightarrow> (\<exists>y. (y \<in> norms_neg \<and> (f (-y)) =  -x)))"
        using calculation(2) norms_def norms_neg_def by auto
      moreover have    "\<forall>x::real. (x<0 \<longrightarrow> (\<exists>y. (y \<in> norms_neg \<and> (?f' (-y)) =  -x)))"
        by (smt (z3) calculation(1) calculation(4) f_inv_into_f normed_gyrolinear_space_axioms normed_gyrolinear_space_def norms_def norms_neg_def rangeI)
      moreover have "\<forall>x::real. (x\<ge> 0 \<or> x<0)"
        by (simp add: linorder_le_less_linear)
      ultimately show ?thesis
      proof -
        { fix rr :: real
          have ff1: "\<forall>r. (r::real) < 0 \<or> 0 \<le> r"
            by (smt (z3))
          have ff2: "\<forall>r ra. sup (ra::real) r = sup r ra"
            by (smt (z3) inf_sup_aci(5))
          have ff3: "\<forall>R Ra. (Ra::real set) \<union> R = R \<union> Ra"
            by (smt (z3) Un_commute)
          have ff4: "\<forall>r ra. (r::real) \<le> sup r ra"
            by simp
          have ff5: "\<forall>R Ra. (R::real set) \<subseteq> Ra \<union> R"
            by (smt (z3) inf_sup_ord(4))
          have ff6: "\<forall>r. (r::real) \<le> r"
            by (smt (z3))
          have ff7: "\<forall>r R Ra. (r::real) \<notin> R \<or> r \<in> Ra \<or> \<not> R \<subseteq> Ra"
            by blast
          have ff8: "\<forall>r. - (- (r::real)) = r"
            using verit_minus_simplify(4) by blast
          have ff9: "- (0::real) = 0"
            by (smt (z3))
          have "\<forall>r ra. r \<notin> norms_all \<or> (if r = 0 then 0 else if r \<in> norms then f r else if r \<in> norms_neg then - f (- r) else undefined) \<noteq> (if ra = 0 then 0 else if ra \<in> norms then f ra else if ra \<in> norms_neg then - f (- ra) else undefined) \<or> ra \<notin> norms_all \<or> r = ra"
            using \<open>\<forall>x y. x \<in> norms_all \<and> y \<in> norms_all \<and> (if x = 0 then 0 else if x \<in> norms then f x else if x \<in> norms_neg then - f (- x) else undefined) = (if y = 0 then 0 else if y \<in> norms then f y else if y \<in> norms_neg then - f (- y) else undefined) \<longrightarrow> x = y\<close> by blast
          then have "\<forall>r. (if r = 0 then 0 else if r \<in> norms then f r else if r \<in> norms_neg then - f (- r) else undefined) \<noteq> (if True then 0 else if 0 \<in> norms then f 0 else if 0 \<in> norms_neg then - f 0 else undefined) \<or> r = 0 \<or> 0 \<notin> norms_all \<or> r \<notin> norms_all"
            using ff9 by (smt (z3))
          then have "(\<exists>r. (if r = 0 then 0 else if r \<in> norms then f r else if r \<in> norms_neg then - f (- r) else undefined) = rr \<and> r \<in> norms_all) \<or> (\<exists>r. (if r = 0 then 0 else if r \<in> norms then f r else if r \<in> norms_neg then - f (- r) else undefined) = rr \<and> r \<in> norms_all)"
            using ff9 ff8 ff7 ff6 ff5 ff4 ff3 ff2 ff1 \<open>\<forall>x<0. \<exists>y. y \<in> norms_neg \<and> f (- y) = - x\<close> \<open>\<forall>x\<ge>0. \<exists>y. y \<in> norms \<and> (if y = 0 then 0 else if y \<in> norms then f y else if y \<in> norms_neg then - f (- y) else undefined) = x\<close> \<open>\<forall>x\<ge>0. \<exists>y. y \<in> norms \<and> f y = x\<close> if_True norms_all_def zero_only_norms_norms_neg by moura }
        then show ?thesis
          by blast
      qed
      
    qed
    moreover have "inj_on ?f' norms_all"
      using "*" inj_on_def by blast
    moreover have ***:"\<forall>x::real. \<exists>y\<in>norms_all. (?f' y = x)"
      using "**" by blast
    moreover have "?f' ` norms_all = UNIV"
    proof-
      have "?f' ` norms_all \<subseteq> UNIV"
        by blast
      moreover have "UNIV \<subseteq> ?f' ` norms_all"
      proof-
        fix x::real
        have "\<exists>y\<in>norms_all. (?f' y = x)"
          using "**" by blast
        then have "x \<in> (?f' ` norms_all)"
          by blast
        then have "\<forall>x::real. (x \<in> (?f' ` norms_all))"
          by (smt (verit, del_insts) "**" image_iff)
        then show ?thesis 
          by blast
      qed
      ultimately show ?thesis
        by force
    qed
    ultimately show " bij_betw ?f' norms_all UNIV" 
      using bij_betw_def by blast
  qed
 
  moreover have fact_fin: " ((\<forall>x::real. \<forall>y::real. ( x\<in>norms_all \<and> y \<in>norms_all \<and> x>y)\<longrightarrow> (?f' x) > (?f' y))
 \<and> (?f' 0) = 0 \<and> bij_betw ?f' norms_all UNIV)"
    using fact1 fact2 by argo
  
  ultimately show ?thesis
    using fact_fin
    by (smt (verit, del_insts))
qed

end

locale normed_gyrolinear_space' = 
  fixes norm'::"'a::gyrolinear_space \<Rightarrow> real"
  fixes f'::"real \<Rightarrow> real"
  assumes "\<forall>a::'a. (norm' a \<ge> 0)"
  assumes "bij_betw f' ((norm' ` UNIV) \<union> ((\<lambda>x. -1 * norm' x) ` UNIV)) UNIV"
  assumes "\<forall>y::real. \<forall>z::real. (( y\<in>  ((norm' ` UNIV) \<union> ((\<lambda>x. -1 * norm' x) ` UNIV)) \<and>
z\<in>  ((norm' ` UNIV) \<union> ((\<lambda>x. -1 * norm' x) ` UNIV)) \<and> y>z)\<longrightarrow> (f' y) > (f' z))"
  assumes "f' 0 = 0"
  assumes "\<forall>x::'a. \<forall>y::'a. f'(norm' (gyroplus x y)) \<le> (f' (norm' x)) + (f' (norm' y))"
  assumes "f' (norm' (scale r x)) = \<bar>r\<bar> * (f' (norm' x))"
  assumes "norm' (gyr u v x) = norm' x"
  assumes "\<forall>x::'a. ((norm' x) = 0 \<longleftrightarrow> x = gyrozero)"
begin

definition norms::"real set" where 
  "norms = norm' ` UNIV"

definition norms_neg::"real set" where 
  "norms_neg = (\<lambda>x. -1 * norm' x) ` UNIV"

definition norms_all::"real set" where 
  "norms_all = norms \<union> norms_neg"

lemma norms_neq_not_empty:
  shows "norms_neg \<noteq> {}"
  using add.inverse_inverse norms_neg_def by fastforce


lemma zero_only_norms_norms_neg:
  assumes "x\<in>norms" "x\<in>norms_neg"
  shows "x=0"
  by (smt (verit, ccfv_threshold) assms(1) assms(2) f_inv_into_f normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_def norms_neg_def)
 

definition norm_oplus_f::"real \<Rightarrow> real \<Rightarrow> real" (infixl " \<oplus>\<^sub>f" 105)
  where "a \<oplus>\<^sub>f b = (if (a\<in>norms_all \<and> b\<in>norms_all) then (inv_into norms_all f') ((f' a) + (f' b))
else undefined)"


definition norm_otimes_f::"real \<Rightarrow> real \<Rightarrow> real" (infixl "\<otimes>\<^sub>f" 105)
  where "r \<otimes>\<^sub>f a = (if (a\<in>norms_all) then (inv_into norms_all f') (r * (f' a))
else undefined)"

lemma vector_space_of_norms:
  shows "vector_space_with_domain norms_all norm_oplus_f 0 norm_otimes_f"
proof
  fix x y
  show "x \<in> norms_all \<Longrightarrow> y \<in> norms_all \<Longrightarrow> x  \<oplus>\<^sub>f y \<in> norms_all"
  proof-
    assume "x\<in>norms_all"
    show "y \<in> norms_all \<Longrightarrow> x  \<oplus>\<^sub>f y \<in> norms_all"
    proof-
      assume "y\<in>norms_all"
      show "x  \<oplus>\<^sub>f y \<in> norms_all"
        by (smt (verit, del_insts) UNIV_I \<open>x \<in> norms_all\<close> \<open>y \<in> norms_all\<close> bij_betw_def inv_into_into norm_oplus_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
    qed
  qed
next
  show "0 \<in> norms_all"
    by (metis Un_iff normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def rangeI)
next 
  fix x y z
  show " x \<in> norms_all \<Longrightarrow>
       y \<in> norms_all \<Longrightarrow> z \<in> norms_all \<Longrightarrow> x  \<oplus>\<^sub>f y  \<oplus>\<^sub>f z = x  \<oplus>\<^sub>f (y  \<oplus>\<^sub>f z)"
  proof-
    assume "x\<in>norms_all"
    show " y \<in> norms_all \<Longrightarrow> z \<in> norms_all \<Longrightarrow> x  \<oplus>\<^sub>f y  \<oplus>\<^sub>f z = x  \<oplus>\<^sub>f (y  \<oplus>\<^sub>f z)"
    proof-
      assume "y \<in> norms_all"
      show "z \<in> norms_all \<Longrightarrow> x  \<oplus>\<^sub>f y  \<oplus>\<^sub>f z = x  \<oplus>\<^sub>f (y  \<oplus>\<^sub>f z)"
      proof-
        assume "z \<in> norms_all"
        show " x  \<oplus>\<^sub>f y  \<oplus>\<^sub>f z = x  \<oplus>\<^sub>f (y  \<oplus>\<^sub>f z)"
        proof-
          have " x  \<oplus>\<^sub>f y = (inv_into norms_all f') ((f' x) + (f' y))"
            by (simp add: \<open>x \<in> norms_all\<close> \<open>y \<in> norms_all\<close> norm_oplus_f_def)
          moreover have "x  \<oplus>\<^sub>f y  \<oplus>\<^sub>f z = (inv_into norms_all f') ((
        f' ( (inv_into norms_all f') ((f' x) + (f' y)))) + (f' z))"
            by (metis (no_types, lifting) UNIV_I \<open>z \<in> norms_all\<close> bij_betw_imp_surj_on calculation inv_into_into norm_oplus_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
          moreover have "x  \<oplus>\<^sub>f y  \<oplus>\<^sub>f z = (inv_into norms_all f') (((f' x)+ (f' y))+(f' z))"
            by (metis (mono_tags, lifting) UNIV_I bij_betw_imp_surj_on calculation(2) f_inv_into_f normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
          moreover have " (y  \<oplus>\<^sub>f z) =  (inv_into norms_all f') ((f' y) + (f' z))"
            by (simp add: \<open>y \<in> norms_all\<close> \<open>z \<in> norms_all\<close> norm_oplus_f_def)
          moreover have " x  \<oplus>\<^sub>f (y  \<oplus>\<^sub>f z) = (inv_into norms_all f') ((f' x) + 
        (f' ((inv_into norms_all f') ((f' y) + (f' z)))))"
            by (metis (mono_tags, lifting) UNIV_I \<open>x \<in> norms_all\<close> bij_betw_def calculation(4) inv_into_into norm_oplus_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
          moreover have " x  \<oplus>\<^sub>f (y  \<oplus>\<^sub>f z) = (inv_into norms_all f') ((f' x) + 
          ((f' y) + (f' z)))"
            by (metis (mono_tags, lifting) UNIV_I bij_betw_imp_surj_on calculation(5) f_inv_into_f normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
          ultimately show ?thesis 
            by argo
        qed
      qed
    qed
  qed
next
  fix x y
  show "x \<in> norms_all \<Longrightarrow> y \<in> norms_all \<Longrightarrow> x  \<oplus>\<^sub>f y = y  \<oplus>\<^sub>f x"
  proof-
    assume "x\<in> norms_all"
    show "y \<in> norms_all \<Longrightarrow> x  \<oplus>\<^sub>f y = y  \<oplus>\<^sub>f x"
    proof-
      assume "y \<in> norms_all"
      show " x \<oplus>\<^sub>f y = y \<oplus>\<^sub>f x"
        by (simp add: add.commute norm_oplus_f_def)
    qed
  qed
next 
  fix x
  show " x \<in> norms_all \<Longrightarrow> x  \<oplus>\<^sub>f 0 = x"
  proof-
    assume "x\<in>norms_all"
    show "x  \<oplus>\<^sub>f 0 = x"
    proof-
      have "x  \<oplus>\<^sub>f 0  = (inv_into norms_all f')  ((f' x) + (f' 0))"
        by (metis (mono_tags, lifting) Un_iff \<open>x \<in> norms_all\<close> norm_oplus_f_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def rangeI)
      then show ?thesis
        by (smt (verit, del_insts) \<open>x \<in> norms_all\<close> bij_betw_def inv_into_f_eq normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
    qed
  qed
next 
  fix x
  show "x \<in> norms_all \<Longrightarrow> \<exists>y\<in>norms_all. x  \<oplus>\<^sub>f y = 0"
  proof-
    assume "x\<in>norms_all"
    show " \<exists>y\<in>norms_all. x  \<oplus>\<^sub>f y = 0"
    proof-
      let ?y = "(inv_into norms_all f') (-(f' x))"
      have " x  \<oplus>\<^sub>f ?y = (inv_into norms_all f') ((f' x) + (f' ?y))"
        by (smt (verit, ccfv_SIG) \<open>x \<in> norms_all\<close> bij_betwE bij_betw_inv_into f_inv_into_f inv_into_into norm_oplus_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def rangeI) 
      moreover have " x  \<oplus>\<^sub>f ?y = (inv_into norms_all f') ((f' x) + (-(f' x)))"
        by (smt (verit, ccfv_SIG) bij_betw_inv_into_right calculation iso_tuple_UNIV_I normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
      moreover have "x  \<oplus>\<^sub>f ?y =(inv_into norms_all f') 0"
        using calculation(2) by force
      moreover have "x  \<oplus>\<^sub>f ?y = 0"
        by (metis (no_types, lifting) Un_iff bij_betw_def calculation(3) inv_into_f_eq normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def rangeI)
      moreover have "?y \<in> norms_all"
        by (metis (no_types, lifting) UNIV_I bij_betw_imp_surj_on inv_into_into normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
      ultimately show ?thesis
        by blast
    qed
  qed
next
  fix x a
  show "x \<in> norms_all \<Longrightarrow> a \<otimes>\<^sub>f x \<in> norms_all"
  proof-
    assume "x\<in>norms_all"
    show " a \<otimes>\<^sub>f x \<in> norms_all"
      by (smt (verit, best) \<open>x \<in> norms_all\<close> bij_betw_imp_surj_on bij_betw_inv_into norm_otimes_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def rangeI)
  qed
next 
  fix x a b
  show "x \<in> norms_all \<Longrightarrow> (a + b) \<otimes>\<^sub>f x = a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (b \<otimes>\<^sub>f x)"
  proof-
    assume "x\<in>norms_all"
    show "(a + b) \<otimes>\<^sub>f x = a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (b \<otimes>\<^sub>f x)"
    proof-
      have "(a + b) \<otimes>\<^sub>f x = (inv_into norms_all f') ((a+b) * (f' x))"
        using \<open>x \<in> norms_all\<close> norm_otimes_f_def by presburger
      moreover have "(a + b) \<otimes>\<^sub>f x = (inv_into norms_all f') (a*(f' x) + b*(f' x))"
        using calculation by argo
      moreover have *:" a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (b \<otimes>\<^sub>f x) = (inv_into norms_all f')
      ((f' (a \<otimes>\<^sub>f x)) + (f' (b \<otimes>\<^sub>f x)))"
      proof -
        have "\<And>f. \<not> normed_gyrolinear_space' norm' f \<or> bij_betw f norms_all UNIV"
          by (metis (no_types) normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_def norms_all_def norms_def)
        then show ?thesis
          by (metis (full_types) UNIV_I \<open>x \<in> norms_all\<close> bij_betw_imp_surj_on inv_into_into norm_oplus_f_def norm_otimes_f_def normed_gyrolinear_space'_axioms)
      qed
      moreover have **:" (inv_into norms_all f')
      ((f' (a \<otimes>\<^sub>f x)) + (f' (b \<otimes>\<^sub>f x))) = (inv_into norms_all f')
    ((f' ((inv_into norms_all f') (a*(f' x)))) +
    (f' ((inv_into norms_all f') (b*(f' x)))))"
        using \<open>x \<in> norms_all\<close> norm_otimes_f_def by presburger
      moreover have "a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (b \<otimes>\<^sub>f x) = (inv_into norms_all f') ((a*(f' x)) + (b*(f' x)))"
        using * **
        by (smt (verit, ccfv_threshold) UNIV_I bij_betw_imp_surj_on f_inv_into_f normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
      ultimately show ?thesis 
        by presburger
    qed
  qed
next
  fix x a b
  show " x \<in> norms_all \<Longrightarrow> a \<otimes>\<^sub>f (b \<otimes>\<^sub>f x) = (a * b) \<otimes>\<^sub>f x"
  proof-
    assume "x\<in>norms_all"
   show "a \<otimes>\<^sub>f (b \<otimes>\<^sub>f x) = (a * b) \<otimes>\<^sub>f x"
      by (smt (verit, best) UNIV_I \<open>x \<in> norms_all\<close> ab_semigroup_mult_class.mult_ac(1) bij_betw_imp_surj_on f_inv_into_f inv_into_into norm_otimes_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
  qed
next 
  fix x
  show "x \<in> norms_all \<Longrightarrow> 1 \<otimes>\<^sub>f x = x"
  proof-
    assume "x\<in>norms_all"
    show " 1 \<otimes>\<^sub>f x = x"
    proof-
      have " 1 \<otimes>\<^sub>f x = (inv_into norms_all f') (1*(f' x))"
        using \<open>x \<in> norms_all\<close> norm_otimes_f_def by presburger
      then show ?thesis 
        by (metis (no_types, lifting) \<open>x \<in> norms_all\<close> bij_betw_inv_into_left lambda_one normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
    qed
  qed
next
  show "\<And>x y a.
       x \<in> norms_all \<Longrightarrow>
       y \<in> norms_all \<Longrightarrow> a \<otimes>\<^sub>f (x  \<oplus>\<^sub>f y) = a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (a \<otimes>\<^sub>f y)"
  proof-
    {
    fix x y a
    assume "x\<in> norms_all \<and> y\<in> norms_all"
    have "a \<otimes>\<^sub>f (x  \<oplus>\<^sub>f y) = (inv_into norms_all f') (a * f' ((inv_into norms_all f') ((f' x) + (f' y))))"
      by (smt (verit, best) UNIV_I \<open>x \<in> norms_all \<and> y \<in> norms_all\<close> bij_betw_imp_surj_on inv_into_into norm_oplus_f_def norm_otimes_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
    moreover have "a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (a \<otimes>\<^sub>f y) = (inv_into norms_all f') ((f' (inv_into norms_all f' (a * (f' x))))+(f' (inv_into norms_all f' (a * (f' y)))))"
      by (smt (verit) \<open>x \<in> norms_all \<and> y \<in> norms_all\<close> bij_betw_def inv_into_into iso_tuple_UNIV_I normed_gyrolinear_space'.norm_oplus_f_def normed_gyrolinear_space'.norm_otimes_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
    ultimately have "a \<otimes>\<^sub>f (x  \<oplus>\<^sub>f y) = a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (a \<otimes>\<^sub>f y)"
      using UNIV_I bij_betw_imp_surj_on f_inv_into_f normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def norms_neg_def ring_class.ring_distribs(1)
      by (smt (verit, best) normed_gyrolinear_space'.norms_neg_def)
  }
   show "\<And>x y a.
       x \<in> norms_all \<Longrightarrow>
       y \<in> norms_all \<Longrightarrow> a \<otimes>\<^sub>f (x  \<oplus>\<^sub>f y) = a \<otimes>\<^sub>f x  \<oplus>\<^sub>f (a \<otimes>\<^sub>f y)"
     using \<open>\<And>y x a. x \<in> norms_all \<and> y \<in> norms_all \<Longrightarrow> a \<otimes>\<^sub>f (x \<oplus>\<^sub>f y) = a \<otimes>\<^sub>f x \<oplus>\<^sub>f (a \<otimes>\<^sub>f y)\<close> by blast
   qed
qed


lemma r2:
  shows "norm' (x \<oplus> y) \<le> (norm' x)  \<oplus>\<^sub>f (norm' y)"
proof-
    have " (f' (norm' (x \<oplus> y))) \<le> (f' (norm' x)) + (f' (norm' y))"
      using normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def by blast
    moreover have "(inv_into norms_all f' (f' (norm' (x \<oplus> y)))) \<le> 
(inv_into norms_all f' ((f' (norm' x)) + (f' (norm' y))))"
      by (smt (verit, ccfv_SIG) UNIV_I bij_betw_def f_inv_into_f inv_into_into normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
  ultimately show ?thesis
    by (metis (no_types, lifting) UnI1 bij_betw_def inv_into_f_eq normed_gyrolinear_space'.norm_oplus_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def rangeI)
qed

lemma r3:
  shows "norm' (r  \<otimes>  x) =  \<bar>r\<bar> \<otimes>\<^sub>f (norm' x)"
  by (smt (verit, best) bij_betw_inv_into_left in_mono inf_sup_ord(3) norm_otimes_f_def normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def rangeI)

lemma one_dim_vs:
  shows "one_dim_vector_space_with_domain norms_all norm_oplus_f 0 norm_otimes_f"
proof-
  have step1: "vector_space_with_domain  norms_all norm_oplus_f 0 norm_otimes_f"
    using vector_space_of_norms by auto
  moreover have step2: "\<forall>y. \<forall>x. (y\<in> norms_all \<and>
 x\<in> norms_all \<and> x\<noteq>0 \<longrightarrow> (\<exists>!r::real. y = r \<otimes>\<^sub>f x))"
  proof
    fix y
    show " \<forall>x. (y\<in> norms_all \<and>
 x\<in> norms_all \<and> x\<noteq>0 \<longrightarrow> (\<exists>!r::real. y = r \<otimes>\<^sub>f x))"
    proof
      fix x
      show "y\<in> norms_all \<and>
 x\<in> norms_all \<and> x\<noteq>0 \<longrightarrow> (\<exists>!r::real. y = r \<otimes>\<^sub>f x)"
      proof
        assume "y\<in> norms_all \<and>
 x\<in> norms_all \<and> x\<noteq>0"
        show "(\<exists>!r::real. y = r \<otimes>\<^sub>f x)"
        proof-
          have "(\<exists>r::real. y = r \<otimes>\<^sub>f x)"
          proof-
            let ?r = "f'(y)/f'(x)"
            have "?r \<otimes>\<^sub>f x = (inv_into norms_all f') (?r * (f' x))"
              by (simp add: \<open>y \<in> norms_all \<and> x \<in> norms_all \<and> x \<noteq> 0\<close> norm_otimes_f_def)
            then show ?thesis 
              by (smt (verit, ccfv_SIG) \<open>y \<in> norms_all \<and> x \<in> norms_all \<and> x \<noteq> 0\<close> bij_betw_inv_into_left nonzero_eq_divide_eq normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def vector_space_of_norms vector_space_with_domain.zero_in_dom)
          qed
          
          moreover have "\<forall>r1.\<forall>r2. (y = r1 \<otimes>\<^sub>f x \<and> y = r2 \<otimes>\<^sub>f x \<longrightarrow> r1=r2)"
          proof
            fix r1 
            show "\<forall>r2. y = r1 \<otimes>\<^sub>f x \<and> y = r2 \<otimes>\<^sub>f x \<longrightarrow> r1=r2"
            proof
              fix r2 
              show "y = r1 \<otimes>\<^sub>f x \<and> y = r2 \<otimes>\<^sub>f x \<longrightarrow> r1=r2"
              proof
                assume "y = r1 \<otimes>\<^sub>f x \<and> y = r2 \<otimes>\<^sub>f x "
                show "r1=r2"
                proof-
                        have "r1 \<otimes>\<^sub>f x = (inv_into norms_all f') (r1 * (f' x))"
            by (simp add: \<open>y \<in> norms_all \<and> x \<in> norms_all \<and> x \<noteq> 0\<close> norm_otimes_f_def)
          moreover have "r2 \<otimes>\<^sub>f x = (inv_into norms_all f') (r2 * (f' x))"
            using \<open>y \<in> norms_all \<and> x \<in> norms_all \<and> x \<noteq> 0\<close> norm_otimes_f_def by presburger
          moreover 
            have "(inv_into norms_all f') (r1 * (f' x)) = (inv_into norms_all f') (r2 * (f' x))"
              using \<open>y = r1 \<otimes>\<^sub>f x \<and> y = r2 \<otimes>\<^sub>f x\<close> calculation(1) calculation(2) by fastforce
            moreover have" f' ( (inv_into norms_all f') (r1 * (f' x))) =
        f'( (inv_into norms_all f') (r2 * (f' x)))"
              using calculation by presburger
            moreover have "r1* (f' x) = r2* (f' x)"
              by (metis (mono_tags, lifting) UNIV_I bij_betw_imp_surj_on calculation(3) inv_into_injective normed_gyrolinear_space'.norms_neg_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def norms_all_def norms_def)
            ultimately show ?thesis
              by (metis (no_types, opaque_lifting) \<open>y \<in> norms_all \<and> x \<in> norms_all \<and> x \<noteq> 0\<close> mult_right_cancel norm_oplus_f_def normed_gyrolinear_space'_axioms normed_gyrolinear_space'_def vector_space_of_norms vector_space_with_domain.add_zero vector_space_with_domain.zero_in_dom)
          qed
          
        qed
      qed
    qed
    ultimately show ?thesis
      by blast
  qed
qed
qed
qed
  ultimately show ?thesis
    by (simp add: one_dim_vector_space_with_domain.intro one_dim_vector_space_with_domain_axioms.intro)
qed

end

locale normed_gyrolinear_space'' = 
  fixes norm'::"'a::gyrolinear_space \<Rightarrow> real"
  fixes oplus'::"real \<Rightarrow> real \<Rightarrow> real"
  fixes otimes'::"real\<Rightarrow>real \<Rightarrow> real"
  assumes "\<forall>a::'a. (norm' a \<ge> 0)"
  assumes ax_space: "one_dim_vector_space_with_domain ((norm' ` UNIV) \<union> ((\<lambda>x. -1 * norm' x) ` UNIV))
      oplus' 0 otimes'"
  assumes ax3: "\<forall>x::'a. \<forall>y::'a. (norm' (gyroplus x y)) \<le> oplus' (norm' x) (norm' y)"
  assumes "(norm' (scale r x)) = otimes' \<bar>r\<bar> (norm' x)"
  assumes "norm' (gyr u v x) = norm' x"
  assumes "\<forall>x::'a. ((norm' x) = 0 \<longleftrightarrow> x = gyrozero)"
begin

definition norms::"real set" where 
  "norms = norm' ` UNIV"

definition norms_neg::"real set" where 
  "norms_neg = (\<lambda>x. -1 * norm' x) ` UNIV"

definition norms_all::"real set" where 
  "norms_all = norms \<union> norms_neg"

lemma norms_neq_not_empty:
  shows "norms_neg \<noteq> {}"
  using add.inverse_inverse norms_neg_def by fastforce


lemma zero_only_norms_norms_neg:
  assumes "x\<in>norms" "x\<in>norms_neg"
  shows "x=0"
 by (smt (verit, ccfv_threshold) assms(1) assms(2) f_inv_into_f normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def norms_def norms_neg_def)

lemma not_trivial_domen_has_pos:
  assumes "\<exists>x. (x\<in>norms_all \<and> x\<noteq>0)"
  shows "\<exists>x. (x\<in>norms \<and> x\<noteq>0)"
  using assms norms_all_def norms_def norms_neg_def by auto

lemma iso_with_real:
  assumes "\<exists>x. (x\<in>norms_all \<and> x\<noteq>0)" (* not trivial domain *)
  shows "\<exists>g. (bij_betw g norms_all UNIV \<and> (g 0) = 0 \<and>
  (\<forall>u.\<forall>v. (u\<in>norms_all \<and> v\<in>norms_all \<longrightarrow> g (oplus' u v) = (g u) + (g v)))
 \<and> (\<forall>u.\<forall>r::real. (u\<in>norms_all \<longrightarrow> g (otimes' r u) = r*(g u)))
)" (*\<and> (\<forall>u. (u\<in>norms \<longrightarrow> (g u)\<ge>0))*)
proof-
  obtain "x" where "x\<in>norms \<and> x\<noteq>0"
    using assms not_trivial_domen_has_pos by presburger
  moreover have "x\<in> norms_all"
    by (simp add: calculation norms_all_def)
  have "\<forall>y. (y\<in>norms_all \<longrightarrow> (\<exists>!r.(y = otimes' r x)))"
    using ax_space  one_dim_vector_space_with_domain_axioms_def
    by (metis \<open>x \<in> norms_all\<close> calculation norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(2))
  let ?g = "\<lambda>y. (THE r. y = otimes' r x)"
  have "bij_betw ?g norms_all UNIV"
  proof-
    have "inj_on ?g norms_all"
      by (smt (verit, best) \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> inj_on_def the_equality)
    moreover have "\<forall>r::real. \<exists>y. (y\<in> norms_all \<and> y = otimes' r x)"
      by (metis \<open>x \<in> norms_all\<close> ax_space norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain.smult_closed)
    moreover have "\<forall>r::real.\<exists>y\<in>norms_all. ?g y = r"
      using \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> calculation(2) by blast
    ultimately show ?thesis 
      by (smt (verit, ccfv_threshold) UNIV_eq_I bij_betw_apply inj_on_imp_bij_betw)
  qed
  moreover have "?g 0 = 0"
  proof-
    obtain "r" where "0 = otimes' r x"
      by (metis \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> ax_space norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain_def vector_space_with_domain.zero_in_dom)
    
    moreover obtain "xx" where "x=norm' xx "
      using norms_all_def 
      using norms_def norms_neg_def
      using \<open>x \<in> norms \<and> x \<noteq> 0\<close> by auto
   
    moreover  have "otimes' 0 x = norm' (0 \<otimes> xx)"
      by (metis (no_types, lifting) calculation(2) norm_zero normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def real_norm_def)
    moreover have "otimes' 0 x = 0"
      by (smt (verit, ccfv_threshold) \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> \<open>x \<in> norms_all\<close> ax_space norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain_def)
    ultimately show ?thesis 
      by (smt (verit) \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> ax_space norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) the1_equality vector_space_with_domain.zero_in_dom)
  qed
  moreover have "\<forall>u.\<forall>v. (u\<in>norms_all \<and> v\<in>norms_all \<longrightarrow> ?g (oplus' u v) = (?g u) + (?g v))"
  proof
    fix u
    show "\<forall>v. (u\<in>norms_all \<and> v\<in>norms_all \<longrightarrow> ?g (oplus' u v) = (?g u) + (?g v))"
    proof
      fix v
      show "u\<in>norms_all \<and> v\<in>norms_all \<longrightarrow> ?g (oplus' u v) = (?g u) + (?g v)"
      proof
        assume "u\<in>norms_all \<and> v\<in>norms_all"
        show " ?g (oplus' u v) = (?g u) + (?g v)"
        proof-
          obtain "a" where "u = otimes' a x"
            using \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> \<open>u \<in> norms_all \<and> v \<in> norms_all\<close> by blast
          moreover obtain "b" where "v = otimes' b x"
            using \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> \<open>u \<in> norms_all \<and> v \<in> norms_all\<close> by blast
          moreover have *:"oplus' u v = otimes' (a+b) x"
            by (metis \<open>x \<in> norms_all\<close> ax_space calculation(1) calculation(2) norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain_def vector_space_with_domain.smult_distr_sadd)
          moreover have "oplus' u v \<in> norms_all"
            by (metis "*" \<open>x \<in> norms_all\<close> ax_space norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain.smult_closed)
          moreover have "?g (oplus' u v) = (a+b)"
            using * 
            using \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> calculation(4) by auto
          ultimately show ?thesis 
            by (smt (verit, del_insts) \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> \<open>u \<in> norms_all \<and> v \<in> norms_all\<close> the1_equality)
        qed
      qed
    qed
  qed
  moreover have "(\<forall>u.\<forall>r::real. (u\<in>norms_all \<longrightarrow> ?g (otimes' r u) = r*(?g u)))"
  proof
    fix u
    show "\<forall>r::real. (u\<in>norms_all \<longrightarrow> ?g (otimes' r u) = r*(?g u))"
    proof
      fix r
      show "u\<in>norms_all \<longrightarrow> ?g (otimes' r u) = r*(?g u)"
      proof
        assume "u\<in>norms_all"
        show "?g (otimes' r u) = r*(?g u)"
        proof-
          obtain "a" where "u = otimes' a x"
            using \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> \<open>u \<in> norms_all\<close> by blast
          moreover have "otimes' r u = otimes' (r*a) x"
            by (metis \<open>x \<in> norms_all\<close> ax_space calculation norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain.smult_assoc)
          moreover have "otimes' r u \<in> norms_all"
            by (metis \<open>u \<in> norms_all\<close> ax_space norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain.smult_closed)
          moreover have "?g (otimes' r u) = (r*a)"
            using \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> calculation(2) calculation(3) by auto
          ultimately show ?thesis 
            by (smt (verit, ccfv_threshold) \<open>\<forall>y. y \<in> norms_all \<longrightarrow> (\<exists>!r. y = otimes' r x)\<close> \<open>u \<in> norms_all\<close> theI')
        qed
      qed
    qed
  qed
 
  ultimately show ?thesis 
    by blast
qed

definition g_iso::"(real\<Rightarrow>real)\<Rightarrow>bool" where
  "g_iso g \<longleftrightarrow> (bij_betw g norms_all UNIV \<and> (g 0) = 0 \<and>
  (\<forall>u.\<forall>v. (u\<in>norms_all \<and> v\<in>norms_all \<longrightarrow> g (oplus' u v) = (g u) + (g v)))
 \<and> (\<forall>u.\<forall>r::real. (u\<in>norms_all \<longrightarrow> g (otimes' r u) = r*(g u))))"

lemma iso_neg_with_real:
  assumes "\<exists>x. (x\<in>norms_all \<and> x\<noteq>0)" (* not trivial domain *)
  shows "g_iso g \<longrightarrow> g_iso (\<lambda>x. -1 * (g x))" 
proof
  assume "g_iso g"
  show " g_iso (\<lambda>x. -1 * (g x))"
  proof-
    have "bij_betw (\<lambda>x. -1 * (g x)) norms_all UNIV"
    proof-
      have "inj_on (\<lambda>x. -1 * (g x)) norms_all"
        by (smt (verit, ccfv_threshold) \<open>g_iso g\<close> bij_betw_imp_inj_on g_iso_def inj_on_def)
      moreover have "\<forall>r::real.\<exists>y\<in>norms_all. ((\<lambda>x. -1 * (g x)) y = r)"
        by (metis UNIV_I \<open>g_iso g\<close> bij_betw_iff_bijections g_iso_def minus_equation_iff mult_cancel_right2 mult_minus_left)
      ultimately show ?thesis 
        by (metis (mono_tags, lifting) UNIV_eq_I bij_betwE bij_betw_imageI)
    qed
    moreover have " (\<lambda>x. -1 * (g x)) 0 = 0"
      using \<open>g_iso g\<close> g_iso_def by force
    moreover have "(\<forall>u.\<forall>v. (u\<in>norms_all \<and> v\<in>norms_all \<longrightarrow>  (\<lambda>x. -1 * (g x)) (oplus' u v)
 = ( (\<lambda>x. -1 * (g x)) u) + ( (\<lambda>x. -1 * (g x)) v)))"
      using \<open>g_iso g\<close> g_iso_def by auto
    moreover have "(\<forall>u.\<forall>r::real. (u\<in>norms_all \<longrightarrow>  (\<lambda>x. -1 * (g x)) (otimes' r u) = r*( (\<lambda>x. -1 * (g x)) u)))"
      using \<open>g_iso g\<close> g_iso_def by auto
    ultimately show ?thesis 
      using g_iso_def by presburger
  qed
qed

lemma iso_with_real_positive_on_norms:
  assumes "\<exists>x. (x\<in>norms_all \<and> x\<noteq>0)" (* not trivial domain *)
  shows "\<exists>g. (g_iso g \<and> (\<forall>x.(x\<in>norms \<longrightarrow> (g x)\<ge>0))
\<and> bij_betw (\<lambda>x. if x \<in> norms then (g x) else undefined) norms {r::real. r\<ge>0})"
proof-
  obtain "xx" where "xx\<in>norms \<and> xx\<noteq>0"
    using assms not_trivial_domen_has_pos by blast
  moreover obtain "x" where "norm' x = xx"
    using calculation norms_def by auto
  moreover obtain "g" where "g_iso g"
    using iso_with_real
    using assms g_iso_def by blast
  let ?g = "if (g xx) < 0 then  (\<lambda>x. -1 * (g x)) else g"
  have *:"?g xx \<ge> 0"
    by force
  moreover have "?g xx \<noteq>0"
  proof (rule ccontr)
    assume "\<not>(?g xx \<noteq>0)"
    have "?g xx = 0"
      using \<open>\<not> (if g xx < 0 then \<lambda>x. - 1 * g x else g) xx \<noteq> 0\<close> by blast
    then have "?g xx = g xx"
      by (smt (verit, ccfv_threshold))
    then have "g xx = 0"
      by (simp add: \<open>(if g xx < 0 then \<lambda>x. - 1 * g x else g) xx = 0\<close>)
    then have "xx=0"
      by (metis \<open>g_iso g\<close> ax_space bij_betw_iff_bijections calculation(1) g_iso_def in_mono inf_sup_ord(3) norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain.zero_in_dom)
    then show False 
      using calculation(1) by blast
  qed
  moreover have "g_iso ?g"
    using \<open>g_iso g\<close> assms iso_neg_with_real by presburger
  moreover have "\<forall>x.(x\<in>norms \<longrightarrow> (?g x)\<ge>0)"
  proof(rule ccontr)
    assume "\<not>(\<forall>x.(x\<in>norms \<longrightarrow> (?g x)\<ge>0))"
    have "\<exists>x. (x\<in>norms \<and> (?g x) < 0)"
      using \<open>\<not> (\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> (if g xx < 0 then \<lambda>x. - 1 * g x else g) x)\<close> by fastforce
    moreover obtain "yy" where "yy \<in> norms \<and> (?g yy) <0"
      using calculation by blast
    moreover obtain "y" where "norm' y = yy"
      using calculation(2) norms_def by auto
    let ?A = "{norm' (r \<otimes> x) | r::real. True}"
    let ?B = "{norm' (r \<otimes> y) | r::real. True}"
    have "?A \<union> ?B \<subseteq> norms"
      using norms_def by auto
    let ?gA = "{(?g a)|a. a\<in>?A}"
    have "?gA = {r::real. r\<ge>0}"
    proof-
      have "\<forall>a. (a\<in>?A \<longrightarrow> ?g a \<ge>0)"
      proof
        fix a
        show "(a\<in>?A \<longrightarrow> ?g a \<ge>0)"
        proof
            assume "a\<in>?A"
            show "?g a \<ge>0"
            proof-
              obtain "r" where "a = norm'  (r \<otimes> x) "
                using \<open>a \<in> {norm' (r \<otimes> x) |r. True}\<close> by blast
              moreover have "?g a = ?g (norm'  (r \<otimes> x) )"
                using calculation by presburger
              moreover have "?g a = ?g ( otimes' \<bar>r\<bar> (norm' x))"
                by (metis calculation(1) normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def)
              moreover have "?g a =  \<bar>r\<bar> * ?g (norm' x)"
                using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> \<open>norm' x = xx\<close> \<open>xx \<in> norms \<and> xx \<noteq> 0\<close> calculation(3) g_iso_def norms_all_def by auto
              ultimately show ?thesis 
                by (simp add: \<open>norm' x = xx\<close>)
            qed
        qed
      qed
      moreover have "?gA \<subseteq> {r::real. r\<ge>0}"
        using calculation by fastforce
      moreover have "{r::real. r\<ge>0} \<subseteq> ?gA"
      proof-
        have "bij_betw ?g norms_all UNIV"
          using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> g_iso_def by blast
        moreover have "\<forall>r::real. (r\<ge>0 \<longrightarrow> r\<in>?gA)"
        proof
          fix r
          show "r\<ge>0 \<longrightarrow> r\<in>?gA"
          proof
            assume "r\<ge>0"
            show "r\<in>?gA"
            proof-
              obtain "r'" where "\<bar>r'\<bar> = r / (?g xx)"
                using  *
                by (meson \<open>0 \<le> r\<close> abs_of_nonneg divide_nonneg_nonneg)
              moreover have "r =  \<bar>r'\<bar> * (?g xx)"
                by (simp add: \<open>(if g xx < 0 then \<lambda>x. - 1 * g x else g) xx \<noteq> 0\<close> calculation)
              moreover have "r =  \<bar>r'\<bar> * (?g (norm' x))"
                using \<open>norm' x = xx\<close> calculation(2) by blast
              moreover have "r = ?g (otimes' \<bar>r'\<bar>  (norm' x))"
                using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> \<open>norm' x = xx\<close> \<open>xx \<in> norms \<and> xx \<noteq> 0\<close> calculation(3) g_iso_def norms_all_def by auto
              moreover have "r = ?g (norm'  (\<bar>r'\<bar>  \<otimes> x))"
                by (smt (verit, del_insts) calculation(4) normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def)
              ultimately show ?thesis 
                by blast
            qed
          qed
        qed
        ultimately show ?thesis 
          by blast
      qed
      
      ultimately show ?thesis 
        by fastforce
    qed
    let ?gB = "{(?g b)|b. b\<in>?B}"
    have "?gB = {r::real. r\<le>0}"


 proof-
      have "\<forall>a. (a\<in>?B \<longrightarrow> ?g a \<le>0)"
      proof
        fix a
        show "(a\<in>?B \<longrightarrow> ?g a \<le>0)"
        proof
            assume "a\<in>?B"
            show "?g a\<le>0"
            proof-
              obtain "r" where "a = norm'  (r \<otimes> y) "
                     using \<open>a \<in> {norm' (r \<otimes> y) |r. True}\<close> by blast
              moreover have "?g a = ?g (norm'  (r \<otimes> y) )"
                using calculation by presburger
              moreover have "?g a = ?g ( otimes' \<bar>r\<bar> (norm' y))"
                by (metis calculation(1) normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def)
              moreover have "?g a =  \<bar>r\<bar> * ?g (norm' y)"
                using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> \<open>norm' y = yy\<close> \<open>yy \<in> norms \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) yy < 0\<close> calculation(3) g_iso_def norms_all_def by auto
               
              ultimately show ?thesis 
                by (simp add: \<open>norm' y = yy\<close> \<open>yy \<in> norms \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) yy < 0\<close> mult_le_0_iff order_less_imp_le)
            qed
        qed
      qed
      moreover have "?gB \<subseteq> {r::real. r\<le>0}"
        using calculation by fastforce
      moreover have "{r::real. r\<le>0} \<subseteq> ?gB"
      proof-
        have "bij_betw ?g norms_all UNIV"
          using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> g_iso_def by blast
        moreover have "\<forall>r::real. (r\<le>0 \<longrightarrow> r\<in>?gB)"
        proof
          fix r
          show "r\<le>0 \<longrightarrow> r\<in>?gB"
          proof
            assume "r\<le>0"
            show "r\<in>?gB"
            proof-
              obtain "r'" where "\<bar>r'\<bar> = r / (?g yy)"
                using  *
                by (metis \<open>r \<le> 0\<close> \<open>yy \<in> norms \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) yy < 0\<close> abs_if divide_less_0_iff less_eq_real_def not_less_iff_gr_or_eq)
              moreover have "r =  \<bar>r'\<bar> * (?g yy)"
                using \<open>yy \<in> norms \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) yy < 0\<close> calculation by auto
              moreover have "r =  \<bar>r'\<bar> * (?g (norm' y))"
                using \<open>norm' y = yy\<close> calculation(2) by blast
              moreover have "r = ?g (otimes' \<bar>r'\<bar>  (norm' y))"
                using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> \<open>norm' y = yy\<close> \<open>yy \<in> norms \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) yy < 0\<close> calculation(3) g_iso_def norms_all_def by auto
              moreover have "r = ?g (norm'  (\<bar>r'\<bar>  \<otimes> y))"
                by (smt (verit, del_insts) calculation(4) normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def)
              ultimately show ?thesis 
                by blast
            qed
          qed
        qed
        ultimately show ?thesis 
          by blast
      qed
      
      ultimately show ?thesis 
        by fastforce
    qed

    let ?gX_norms = "{(?g x)|x. x\<in>norms}"
    let ?gX_norms_all = "{(?g x)|x. x\<in>norms_all}"
    let ?gA_union_B = "{(?g x)|x. x\<in> ?A\<union>?B}"
    have "?gA_union_B \<subseteq> ?gX_norms"
      using \<open>{norm' (r \<otimes> x) |r. True} \<union> {norm' (r \<otimes> y) |r. True} \<subseteq> norms\<close> by force
    moreover have "?gA_union_B = ?gA \<union> ?gB"
    proof-
      have "?gA_union_B \<subseteq> ?gA \<union> ?gB"
        by blast
      moreover have "?gA \<union> ?gB \<subseteq> ?gA_union_B"
        by blast
      ultimately show ?thesis
        by force
    qed
    moreover have "?gA_union_B = UNIV"
      using \<open>{(if g xx < 0 then \<lambda>x. - 1 * g x else g) a |a. a \<in> {norm' (r \<otimes> x) |r. True}} = {r. 0 \<le> r}\<close> \<open>{(if g xx < 0 then \<lambda>x. - 1 * g x else g) b |b. b \<in> {norm' (r \<otimes> y) |r. True}} = {r. r \<le> 0}\<close> calculation(4) by force
    moreover have "UNIV \<subseteq> ?gX_norms"
      using calculation(3) calculation(5) by argo
   (* moreover have "?gX_norms \<subset> ?gX_norms_all"
    proof-
      have "\<forall>a. (a\<in> ?gX_norms \<longrightarrow> a\<in> ?gX_norms_all)"
        using norms_all_def by fastforce*)
      (*moreover have "\<exists>a. (a\<in>?gX_norms_all \<and> \<not>a\<in>?gX_norms)"
      proof-*)
        obtain "a" where "a\<in>norms_all \<and> \<not>a\<in>norms"
          by (metis (mono_tags, lifting) Un_iff add.inverse_inverse assms mult_minus1 norms_all_def norms_def norms_neg_def rangeE rangeI zero_only_norms_norms_neg)
        let ?a = "?g a"
        have "?a \<in> ?gX_norms_all "

          using \<open>a \<in> norms_all \<and> a \<notin> norms\<close> by blast

        moreover have "\<not>?a\<in> ?gX_norms"
        proof(rule ccontr)
          assume "\<not>(\<not>?a\<in> ?gX_norms)"
          have "?a\<in>?gX_norms"
            using \<open>\<not> (if g xx < 0 then \<lambda>x. - 1 * g x else g) a \<notin> {(if g xx < 0 then \<lambda>x. - 1 * g x else g) x |x. x \<in> norms}\<close> by blast
          then obtain "b" where "b\<in>norms \<and> ?g b = ?a"
            by force
         
            then show False using  \<open>a \<in> norms_all \<and> a \<notin> norms\<close> \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> bij_betw_inv_into_left g_iso_def inf_sup_ord(3) norms_all_def subsetD
              by (smt (verit, ccfv_threshold) \<open>g_iso g\<close>)
          qed
          moreover have "False" 

            using \<open>UNIV \<subseteq> {(if g xx < 0 then \<lambda>x. - 1 * g x else g) x |x. x \<in> norms}\<close> calculation(7) by blast
            
    ultimately show False 
      by auto
  qed
  

  moreover have " bij_betw (\<lambda>x. if x \<in> norms then (?g x) else undefined) norms {r::real. r\<ge>0}"
  proof-
    let ?f = "(\<lambda>x. if x \<in> norms then (?g x) else undefined)"
     let ?A = "{norm' (r \<otimes> x) | r::real. True}"
     let ?gA = "{(?g a)|a. a\<in>?A}"
     have s1:"?gA = {r::real. r\<ge>0}"
        proof-
      have "\<forall>a. (a\<in>?A \<longrightarrow> ?g a \<ge>0)"
      proof
        fix a
        show "(a\<in>?A \<longrightarrow> ?g a \<ge>0)"
        proof
            assume "a\<in>?A"
            show "?g a \<ge>0"
            proof-
              obtain "r" where "a = norm'  (r \<otimes> x) "
                using \<open>a \<in> {norm' (r \<otimes> x) |r. True}\<close> by blast
              moreover have "?g a = ?g (norm'  (r \<otimes> x) )"
                using calculation by presburger
              moreover have "?g a = ?g ( otimes' \<bar>r\<bar> (norm' x))"
                by (metis calculation(1) normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def)
              moreover have "?g a =  \<bar>r\<bar> * ?g (norm' x)"
                using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> \<open>norm' x = xx\<close> \<open>xx \<in> norms \<and> xx \<noteq> 0\<close> calculation(3) g_iso_def norms_all_def by auto
              ultimately show ?thesis 
                by (simp add: \<open>norm' x = xx\<close>)
            qed
        qed
      qed
      moreover have "?gA \<subseteq> {r::real. r\<ge>0}"
        using calculation by fastforce
      moreover have "{r::real. r\<ge>0} \<subseteq> ?gA"
      proof-
        have "bij_betw ?g norms_all UNIV"
          using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> g_iso_def by blast
        moreover have "\<forall>r::real. (r\<ge>0 \<longrightarrow> r\<in>?gA)"
        proof
          fix r
          show "r\<ge>0 \<longrightarrow> r\<in>?gA"
          proof
            assume "r\<ge>0"
            show "r\<in>?gA"
            proof-
              obtain "r'" where "\<bar>r'\<bar> = r / (?g xx)"
                using  *
                by (meson \<open>0 \<le> r\<close> abs_of_nonneg divide_nonneg_nonneg)
              moreover have "r =  \<bar>r'\<bar> * (?g xx)"
                by (simp add: \<open>(if g xx < 0 then \<lambda>x. - 1 * g x else g) xx \<noteq> 0\<close> calculation)
              moreover have "r =  \<bar>r'\<bar> * (?g (norm' x))"
                using \<open>norm' x = xx\<close> calculation(2) by blast
              moreover have "r = ?g (otimes' \<bar>r'\<bar>  (norm' x))"
                using \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> \<open>norm' x = xx\<close> \<open>xx \<in> norms \<and> xx \<noteq> 0\<close> calculation(3) g_iso_def norms_all_def by auto
              moreover have "r = ?g (norm'  (\<bar>r'\<bar>  \<otimes> x))"
                by (smt (verit, del_insts) calculation(4) normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def)
              ultimately show ?thesis 
                by blast
            qed
          qed
        qed
        ultimately show ?thesis 
          by blast
      qed
      
      ultimately show ?thesis 
        by fastforce
    qed
     moreover have s2:"\<forall>y. (?g (norm' y) \<ge>0)"
       using \<open>\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> (if g xx < 0 then \<lambda>x. - 1 * g x else g) x\<close> norms_def by blast
     moreover have "norms = ?A"
     proof-
       have "\<forall>y. (?g (norm' y) \<in> ?gA)"
         using s1 s2 by blast
       moreover have "norms \<subseteq> ?A"
       proof-
         have "\<forall>y. (y\<in>norms \<longrightarrow> y\<in>?A)"
         proof
           fix y
           show "y\<in>norms \<longrightarrow> y\<in>?A"
           proof
             assume "y\<in>norms"
             show "y\<in>?A"
             proof-
               obtain "yy" where "y=norm' yy"
                 using \<open>y \<in> norms\<close> norms_def by auto
               moreover have "?g (norm' yy) \<in>?gA"
                 using \<open>\<forall>y. (if g xx < 0 then \<lambda>x. - 1 * g x else g) (norm' y) \<in> {(if g xx < 0 then \<lambda>x. - 1 * g x else g) a |a. a \<in> {norm' (r \<otimes> x) |r. True}}\<close> by blast
               moreover have "norm' yy \<in> ?A"
               proof-
                 obtain "h" where "h \<in> ?A \<and> ?g h = ?g (norm' yy)"
                   using calculation(2) by fastforce
                 moreover have "?g h \<ge>0"
                   using calculation s2 by blast
                
                 moreover {
                   assume "?g = g"
                   have " g h = g (norm' yy)"
                     by (smt (verit, ccfv_SIG) calculation(1))
                   
                   moreover have "h=norm' yy"
                   proof-
                     have "h\<in>norms"
                       using \<open>h \<in> {norm' (r \<otimes> x) |r. True} \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) h = (if g xx < 0 then \<lambda>x. - 1 * g x else g) (norm' yy)\<close> norms_def by force
                     moreover have "norm' yy \<in> norms"
                       using \<open>y = norm' yy\<close> \<open>y \<in> norms\<close> by blast
                     ultimately show ?thesis 
                       by (metis \<open>g h = g (norm' yy)\<close> \<open>g_iso g\<close> bij_betw_inv_into_left g_iso_def inf_sup_ord(3) norms_all_def subset_iff)
                   qed
                   ultimately have ?thesis
                     using \<open>h \<in> {norm' (r \<otimes> x) |r. True} \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) h = (if g xx < 0 then \<lambda>x. - 1 * g x else g) (norm' yy)\<close> by blast
                 }
                   moreover {
                   assume "?g = (\<lambda>x. -1 * (g x))"
                   have " g h = g (norm' yy)"
                     by (smt (verit, ccfv_SIG) calculation(1))
                   
                   moreover have "h=norm' yy"
                   proof-
                     have "h\<in>norms"
                       using \<open>h \<in> {norm' (r \<otimes> x) |r. True} \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) h = (if g xx < 0 then \<lambda>x. - 1 * g x else g) (norm' yy)\<close> norms_def by force
                     moreover have "norm' yy \<in> norms"
                       using \<open>y = norm' yy\<close> \<open>y \<in> norms\<close> by blast
                     ultimately show ?thesis 
                       by (metis \<open>g h = g (norm' yy)\<close> \<open>g_iso g\<close> bij_betw_inv_into_left g_iso_def inf_sup_ord(3) norms_all_def subset_iff)
                   qed
                   ultimately have ?thesis
                     using \<open>h \<in> {norm' (r \<otimes> x) |r. True} \<and> (if g xx < 0 then \<lambda>x. - 1 * g x else g) h = (if g xx < 0 then \<lambda>x. - 1 * g x else g) (norm' yy)\<close> by blast
                 }
                 ultimately show ?thesis 
                   by argo
               qed
               ultimately show ?thesis 
                 by fastforce
             qed
         qed
       qed
        show ?thesis 
          using \<open>\<forall>y. y \<in> norms \<longrightarrow> y \<in> {norm' (r \<otimes> x) |r. True}\<close> by blast
      qed
      ultimately show ?thesis 
        using norms_def by fastforce
    qed
     moreover have step1:"inj_on ?f  norms"
     proof-
       have "\<forall>x.\<forall>y. (x\<in> norms \<and> y\<in> norms \<and> (?f x) = (?f y) \<longrightarrow> x=y)"
       proof
         fix x 
         show "\<forall>y. (x\<in> norms \<and> y\<in> norms \<and> (?f x) = (?f y) \<longrightarrow> x=y)"
         proof
           fix y 
           show " (x\<in> norms \<and> y\<in> norms \<and> (?f x) = (?f y) \<longrightarrow> x=y)"
             by (metis \<open>g_iso (if g xx < 0 then \<lambda>x. - 1 * g x else g)\<close> bij_betw_imp_inj_on g_iso_def inf_sup_ord(3) inj_on_def norms_all_def subsetD)
         qed
       qed
       then show ?thesis
         using inj_on_def by blast
     qed
     moreover have "\<forall>r::real. (r\<ge>0 \<longrightarrow> (\<exists>x. (x\<in> norms \<and> ?f x = r)))"
       by (smt (verit) calculation(3) mem_Collect_eq s1)
       
     moreover have step2:"\<forall>r::real. (r\<ge>0 \<longrightarrow> (\<exists>x\<in> norms.( ?f x = r)))"
 
       using calculation(5) by blast
     moreover have "\<forall>r\<in>{x::real. x\<ge>0}. (\<exists>x\<in>norms. (?f x = r))"
       using step2
       by blast
     moreover have **:"?f=(\<lambda>x. if x \<in> norms then (?g x) else undefined)"
       by meson
     moreover have "?f ` norms = {r::real. r\<ge>0}"
       by (smt (verit) Collect_cong Setcompr_eq_image calculation(3) s1)
     ultimately show ?thesis 
       by (simp add: bij_betw_def)
    
   qed
 
  ultimately show ?thesis
    by blast
qed




lemma comparing_norms_help:
  assumes "x\<in>norms" "y\<in>norms_all"
  "x\<le>y"
shows "y\<in> norms"
proof-
  have "x < y \<or> x=y"
    using assms(3) by argo
  moreover {
    assume "x<y"
    have ?thesis 
      by (smt (verit) Un_iff \<open>x < y\<close> add_0 add_uminus_conv_diff assms(1) assms(2) full_SetCompr_eq linorder_not_less mem_Collect_eq mult_minus1 normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def norms_all_def norms_def norms_neg_def order_le_less_trans)
  }
  moreover {
    assume "x=y"
    have ?thesis 
      using \<open>x = y\<close> assms(1) by blast
  }
  ultimately show ?thesis by blast
qed

lemma existence_of_f:
 assumes "\<exists>x. (x\<in>norms_all \<and> x\<noteq>0)" (* not trivial domain *)
  shows "\<exists>f. (bij_betw f norms {x::real. x\<ge>0}
\<and>  (\<forall>y::real. \<forall>z::real. (( y\<in> norms \<and>
z\<in>  norms \<and> y>z)\<longrightarrow> (f y) > (f z)))
  \<and> (\<forall>x. \<forall>y. f(norm' (x \<oplus> y)) \<le> (f (norm' x)) + (f (norm' y)))
\<and> (\<forall>r::real. (\<forall>x. (f (norm' (r \<otimes> x)) = \<bar>r\<bar> * (f (norm' x))))))"
proof-
  obtain "g" where "(g_iso g \<and> (\<forall>x.(x\<in>norms \<longrightarrow> (g x)\<ge>0))
\<and> bij_betw (\<lambda>x. if x \<in> norms then (g x) else undefined) norms {r::real. r\<ge>0})"
    using  iso_with_real_positive_on_norms
    assms by blast
  let ?f = "\<lambda>x. if x \<in> norms then (g x) else undefined"
  have "\<forall>\<alpha>::real. \<forall>\<beta>::real. \<forall>x. ((0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>) \<longrightarrow> ((otimes' \<alpha>  (norm' x)) \<le> (otimes' \<beta>  (norm' x))))"
  proof
    fix \<alpha> 
    show " \<forall>\<beta>::real. \<forall>x.((0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>) \<longrightarrow> ((otimes' \<alpha>  (norm' x)) \<le> (otimes' \<beta>  (norm' x))))"
    proof
      fix \<beta>
      show " \<forall>x.((0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>) \<longrightarrow> ((otimes' \<alpha>  (norm' x)) \<le> (otimes' \<beta>  (norm' x))))"
      proof
        fix x 
        show "((0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>) \<longrightarrow> ((otimes' \<alpha>  (norm' x)) \<le> (otimes' \<beta>  (norm' x))))"
        proof
          assume "0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>"
          show "((otimes' \<alpha>  (norm' x)) \<le> (otimes' \<beta>  (norm' x)))"
          proof-
            have "otimes' \<alpha>  (norm' x) = norm' (\<alpha> \<otimes> x)"
              by (metis \<open>0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>\<close> abs_of_nonneg normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def)
            moreover have " norm' (\<alpha> \<otimes> x) = norm' (((\<beta>+\<alpha>)/2 - (\<beta>-\<alpha>)/2)\<otimes> x)"
              by (simp add: add_divide_distrib diff_divide_distrib)
            moreover have "norm' (((\<beta>+\<alpha>)/2 - (\<beta>-\<alpha>)/2)\<otimes> x) = 
            norm' (((\<beta>+\<alpha>)/2) \<otimes> x \<oplus>  (- (\<beta>-\<alpha>)/2) \<otimes> x )"
              by (metis add.commute divide_minus_left scale_distrib uminus_add_conv_diff)
            moreover have " norm' (((\<beta>+\<alpha>)/2) \<otimes> x \<oplus>  (- (\<beta>-\<alpha>)/2) \<otimes> x )
        \<le>  oplus' (norm' (((\<beta>+\<alpha>)/2)\<otimes> x)) (norm' ((-(\<beta>-\<alpha>)/2)  \<otimes> x))"
              using  ax3
              by blast
            moreover have "-(\<beta>-\<alpha>)/2 \<le>0"
              by (simp add: \<open>0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>\<close>)
            moreover have "(\<beta>+\<alpha>)/2 \<ge>0"
              using \<open>0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta>\<close> by auto
            moreover have *:"(norm' (((\<beta>+\<alpha>)/2)\<otimes> x)) =(otimes' ((\<beta>+\<alpha>)/2) (norm' x))"
              by (smt (verit, ccfv_threshold) calculation(6) normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def)
            moreover have " \<bar>-(\<beta>-\<alpha>)/2\<bar> = (\<beta>-\<alpha>)/2 "
              using calculation(5) by force
            moreover have **:"(norm' ((-(\<beta>-\<alpha>)/2)\<otimes> x)) =(otimes' ((\<beta>-\<alpha>)/2) (norm' x))"
              by (metis calculation(8) normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def)
            moreover have "  oplus' (norm' (((\<beta>+\<alpha>)/2)\<otimes> x)) (norm' ((-(\<beta>-\<alpha>)/2)  \<otimes> x)) =
       oplus' (otimes' ((\<beta>+\<alpha>)/2) (norm' x)) (otimes' ( (\<beta>-\<alpha>)/2) (norm' x)) "
              using * **
              by presburger
            moreover have "oplus' (otimes' ((\<beta>+\<alpha>)/2) (norm' x)) (otimes' ( (\<beta>-\<alpha>)/2) (norm' x))
      = otimes' ((\<beta>+\<alpha>)/2 + ((\<beta>-\<alpha>)/2)) (norm' x)"
              by (metis Un_iff ax_space one_dim_vector_space_with_domain_def rangeI vector_space_with_domain.smult_distr_sadd)
            moreover have " otimes' ((\<beta>+\<alpha>)/2 + ((\<beta>-\<alpha>)/2)) (norm' x) = otimes' \<beta> (norm' x)"
              by argo
            ultimately show ?thesis 
              by linarith
          qed
        qed
      qed
    qed
  qed
  moreover have "\<forall>\<alpha>::real. \<forall>\<beta>::real. \<forall>x. ((0 < \<alpha> \<and> \<alpha> < \<beta> \<and> x\<noteq>gyrozero) \<longrightarrow> ((otimes' \<alpha>  (norm' x)) < (otimes' \<beta>  (norm' x))))"
  proof -
    have f1: "\<forall>f fa fb. normed_gyrolinear_space'' f fa fb = (((\<forall>a. 0 \<le> f (a::'a)) \<and> one_dim_vector_space_with_domain (range f \<union> range (\<lambda>a. - 1 * f a)) fa 0 fb \<and> (\<forall>a aa. f (a \<oplus> aa) \<le> fa (f a) (f aa))) \<and> (\<forall>r a. f (r \<otimes> a) = fb (if r < 0 then - r else r) (f a)) \<and> (\<forall>a aa ab. f (gyr a aa ab) = f ab) \<and> (\<forall>a. (f a = 0) = (a = 0\<^sub>g)))"
      by (simp add: abs_if_raw normed_gyrolinear_space''_def)
    obtain rr :: "real \<Rightarrow> real" where
      f2: "bij_betw rr norms_all UNIV \<and> 0 = rr 0 \<and> (\<forall>r ra. r \<in> norms_all \<and> ra \<in> norms_all \<longrightarrow> rr (oplus' r ra) = rr r + rr ra) \<and> (\<forall>r ra. r \<in> norms_all \<longrightarrow> rr (otimes' ra r) = ra * rr r)"
      using assms iso_with_real by auto
    have "\<forall>a. (0 = norm' a) = (0\<^sub>g = a)"
      using f1 by (smt (z3) normed_gyrolinear_space''_axioms)
    then show ?thesis
      using f2 by (smt (z3) UnI2 bij_betw_inv_into_left calculation mult_right_cancel norms_all_def norms_def rangeI sup_commute)
  qed
  moreover obtain "xx0" where "xx0\<in>norms \<and> xx0\<noteq>0"
    using assms not_trivial_domen_has_pos by blast
  moreover obtain "x0" where "xx0 = norm' x0"
    using calculation(3) norms_def by auto
  moreover have mon:"(\<forall>y z. y \<in> norms \<and> z \<in> norms \<and> z < y \<longrightarrow> ?f z < ?f y)"
  proof
    fix y 
    show "\<forall>z. (y \<in> norms \<and> z \<in> norms \<and> z < y \<longrightarrow> ?f z < ?f y)"
    proof
      fix z 
      show "y \<in> norms \<and> z \<in> norms \<and> z < y \<longrightarrow> ?f z < ?f y"
      proof
        assume "y \<in>norms \<and> z \<in> norms \<and> z < y"
        show "?f z < ?f y"
        proof-
          let ?alpha = "(?f y)/(?f (norm' x0))"
          let ?beta = "(?f z)/(?f (norm' x0))"
          have "otimes' ?alpha (norm' x0) = y"
            by (smt (verit, del_insts) \<open>g_iso g \<and> (\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> g x) \<and> bij_betw (\<lambda>x. if x \<in> norms then g x else undefined) norms {r. 0 \<le> r}\<close> \<open>y \<in> norms \<and> z \<in> norms \<and> z < y\<close> ax_space bij_betw_imp_inj_on calculation(3) calculation(4) g_iso_def in_mono inf_sup_ord(3) inj_on_def nonzero_eq_divide_eq norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) vector_space_with_domain.smult_closed vector_space_with_domain.zero_in_dom)
          moreover have "otimes' ?beta (norm' x0) = z"
            by (smt (verit, del_insts) \<open>g_iso g \<and> (\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> g x) \<and> bij_betw (\<lambda>x. if x \<in> norms then g x else undefined) norms {r. 0 \<le> r}\<close> \<open>xx0 = norm' x0\<close> \<open>xx0 \<in> norms \<and> xx0 \<noteq> 0\<close> \<open>y \<in> norms \<and> z \<in> norms \<and> z < y\<close> ax_space bij_betw_imp_inj_on g_iso_def inf_sup_ord(3) inj_on_def nonzero_eq_divide_eq norms_all_def norms_def norms_neg_def one_dim_vector_space_with_domain.axioms(1) subset_iff vector_space_with_domain.smult_closed vector_space_with_domain.zero_in_dom)
          moreover have "?alpha \<ge> 0 \<and> ?beta \<ge>0"
             using \<open>g_iso g \<and> (\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> g x) \<and> bij_betw (\<lambda>x. if x \<in> norms then g x else undefined) norms {r. 0 \<le> r}\<close> \<open>xx0 = norm' x0\<close> \<open>xx0 \<in> norms \<and> xx0 \<noteq> 0\<close> \<open>y \<in> norms \<and> z \<in> norms \<and> z < y\<close> by auto
           moreover have "0 < ?alpha \<and> ?alpha < ?beta \<longleftrightarrow> 0<y \<and> y<z"
             by (smt (verit, ccfv_threshold) \<open>\<forall>\<alpha> \<beta> x. 0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta> \<longrightarrow> otimes' \<alpha> (norm' x) \<le> otimes' \<beta> (norm' x)\<close> \<open>y \<in> norms \<and> z \<in> norms \<and> z < y\<close> calculation(1) calculation(2))
           moreover have "0<?alpha \<and> ?alpha < ?beta \<longleftrightarrow> 0 \<le> (?f y) \<and> (?f y) < (?f z)"
             by (smt (verit, best) \<open>\<forall>\<alpha> \<beta> x. 0 \<le> \<alpha> \<and> \<alpha> \<le> \<beta> \<longrightarrow> otimes' \<alpha> (norm' x) \<le> otimes' \<beta> (norm' x)\<close> \<open>y \<in> norms \<and> z \<in> norms \<and> z < y\<close> calculation(1) calculation(2) calculation(3) div_by_0 frac_less zero_le_divide_iff)
           ultimately show ?thesis
             using \<open>g_iso g \<and> (\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> g x) \<and> bij_betw (\<lambda>x. if x \<in> norms then g x else undefined) norms {r. 0 \<le> r}\<close> \<open>y \<in> norms \<and> z \<in> norms \<and> z < y\<close> by auto
         qed
      qed
    qed
  qed
  moreover have " (\<forall>x y. ?f (norm' (x \<oplus> y)) \<le> ?f (norm' x) + ?f (norm' y))"
  proof
    fix x 
    show "\<forall>y. (?f (norm' (x \<oplus> y)) \<le> ?f (norm' x) + ?f (norm' y))"
    proof
      fix y
      show " (?f (norm' (x \<oplus> y)) \<le> ?f (norm' x) + ?f (norm' y))"
      proof-
        have "norm' x\<in>norms"
          using norms_def by blast
        moreover have "norm' y \<in> norms"
          using norms_def by blast
        moreover have "norm' (x \<oplus> y)\<in> norms"
          using norms_def by blast
        moreover have "norm' (x \<oplus> y) \<le> oplus' (norm' x) (norm' y)"
          using ax3 by blast
        moreover have "(?f (norm' (x \<oplus> y))) \<le> (?f (oplus' (norm' x) (norm' y)))"
        proof-
          have "norm' (x \<oplus> y) \<le> oplus' (norm' x) (norm' y) \<or> norm' (x \<oplus> y) = oplus' (norm' x) (norm' y)"
            using calculation(4) by blast
          moreover {
            assume st1:"norm' (x \<oplus> y) < oplus' (norm' x) (norm' y)"
            have "norm' x \<in> norms"
              using norms_def by blast
            moreover have "norm' y \<in> norms"
              using norms_def by blast
            moreover have "vector_space_with_domain norms_all oplus' 0 otimes'"
              using ax_space norms_def 
              one_dim_vector_space_with_domain_def
              by (metis norms_all_def norms_neg_def)
            moreover have "oplus' (norm' x) (norm' y) \<in> norms_all"
              by (metis Un_iff calculation(1) calculation(2) calculation(3) norms_all_def vector_space_with_domain.add_closed)
            moreover have st2:"norm' (x \<oplus> y)\<in> norms"
              by (simp add: \<open>norm' (x \<oplus> y) \<in> norms\<close>)
            moreover have st3:"oplus' (norm' x) (norm' y) \<in> norms"  
              using ax3 calculation(4) comparing_norms_help st2 by blast
            
moreover have "(?f (norm' (x \<oplus> y))) < (?f (oplus' (norm' x) (norm' y)))"
              using mon st1 st2 st3
              by blast
            ultimately have ?thesis 
              by linarith
          }
          moreover {
              assume "norm' (x \<oplus> y) = oplus' (norm' x) (norm' y)"
              then have ?thesis 
                by auto
            }
            ultimately show ?thesis
              by fastforce
        qed 
        moreover have " (?f (oplus' (norm' x) (norm' y))) = (?f (norm' x)) + (?f (norm' y))"
        proof-
          have f1:"norm' (x \<oplus> y) \<le> oplus' (norm' x) (norm' y)"
            using ax3 by blast
          moreover have f2:"norm' (x \<oplus> y) \<in> norms"
            by (simp add: \<open>norm' (x \<oplus> y) \<in> norms\<close>)
          moreover have f3:"vector_space_with_domain norms_all oplus' 0 otimes'"
              using ax_space norms_def 
              one_dim_vector_space_with_domain_def
              by (metis norms_all_def norms_neg_def)
          moreover have "oplus' (norm' x) (norm' y)\<in> norms"
              by (metis UnI1 \<open>norm' x \<in> norms\<close> \<open>norm' y \<in> norms\<close> f1 f2 f3 normed_gyrolinear_space''.comparing_norms_help normed_gyrolinear_space''_axioms norms_all_def vector_space_with_domain.add_closed)
            ultimately show ?thesis 
              using \<open>g_iso g \<and> (\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> g x) \<and> bij_betw (\<lambda>x. if x \<in> norms then g x else undefined) norms {r. 0 \<le> r}\<close> \<open>norm' x \<in> norms\<close> \<open>norm' y \<in> norms\<close> g_iso_def norms_all_def by force
          qed
          ultimately show ?thesis 
            by force
      qed
    qed
  qed

  moreover have "(\<forall>r::real. (\<forall>x. (?f (norm' (r \<otimes> x)) = \<bar>r\<bar> * (?f (norm' x)))))"
    by (smt (verit, ccfv_SIG) Un_iff \<open>g_iso g \<and> (\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> g x) \<and> bij_betw (\<lambda>x. if x \<in> norms then g x else undefined) norms {r. 0 \<le> r}\<close> g_iso_def normed_gyrolinear_space''_axioms normed_gyrolinear_space''_def norms_all_def norms_def rangeI)

  ultimately show ?thesis
    using \<open>g_iso g \<and> (\<forall>x. x \<in> norms \<longrightarrow> 0 \<le> g x) \<and> bij_betw (\<lambda>x. if x \<in> norms then g x else undefined) norms {r. 0 \<le> r}\<close> by blast
qed



end



end

