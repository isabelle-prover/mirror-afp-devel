(*  Title:   Exponent_QuasiBorel.thy
    Author:  Michikazu Hirata, Tokyo Institute of Technology
*)

subsection \<open>Function Spaces\<close>

theory Exponent_QuasiBorel
  imports "CoProduct_QuasiBorel"
begin

subsubsection \<open> Function Spaces  \<close>
definition exp_qbs_Mx :: "['a quasi_borel, 'b quasi_borel] \<Rightarrow> (real \<Rightarrow> 'a => 'b) set" where
"exp_qbs_Mx X Y \<equiv> {g :: real \<Rightarrow> 'a \<Rightarrow> 'b. case_prod g \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q X \<rightarrow>\<^sub>Q Y} "

definition exp_qbs :: "['a quasi_borel, 'b quasi_borel] \<Rightarrow> ('a \<Rightarrow> 'b) quasi_borel" (infixr "\<Rightarrow>\<^sub>Q" 61) where
"X \<Rightarrow>\<^sub>Q Y \<equiv> Abs_quasi_borel (X \<rightarrow>\<^sub>Q Y, exp_qbs_Mx X Y)"


lemma exp_qbs_f[simp]: "exp_qbs_Mx X Y \<subseteq> UNIV \<rightarrow> (X :: 'a quasi_borel) \<rightarrow>\<^sub>Q (Y :: 'b quasi_borel)"
proof(auto intro!: qbs_morphismI)
  fix f \<alpha> r
  assume h:"f \<in> exp_qbs_Mx X Y"
           "\<alpha> \<in> qbs_Mx X"
  have "f r \<circ> \<alpha> = (\<lambda>y. case_prod f (r,y)) \<circ> \<alpha>"
    by auto
  also have "... \<in> qbs_Mx Y"
    using qbs_morphism_Pair1'[of r "\<real>\<^sub>Q" "case_prod f" X Y] h
    by(auto simp: exp_qbs_Mx_def)
  finally show "f r \<circ> \<alpha> \<in> qbs_Mx Y" .
qed

lemma exp_qbs_closed1: "qbs_closed1 (exp_qbs_Mx X Y)"
proof(rule qbs_closed1I)
  fix a
  fix f
  assume h:"a \<in> exp_qbs_Mx X Y"
           "f \<in> real_borel \<rightarrow>\<^sub>M real_borel"
  have "a \<circ> f = (\<lambda>r y. case_prod a (f r,y))" by auto
  moreover have "case_prod ... \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q X \<rightarrow>\<^sub>Q Y"
  proof -
    have "case_prod (\<lambda>r y. case_prod a (f r,y)) = case_prod a \<circ> map_prod f id"
      by auto
    also have "... \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q X \<rightarrow>\<^sub>Q Y"
      using h
      by(auto intro!: qbs_morphism_comp qbs_morphism_map_prod simp: exp_qbs_Mx_def)
    finally show ?thesis .
  qed
  ultimately show "a \<circ> f \<in> exp_qbs_Mx X Y"
    by (simp add: exp_qbs_Mx_def)
qed

lemma exp_qbs_closed2: "qbs_closed2 (X \<rightarrow>\<^sub>Q Y) (exp_qbs_Mx X Y)"
  by(auto intro!: qbs_closed2I qbs_morphism_snd'' simp: exp_qbs_Mx_def split_beta')

lemma exp_qbs_closed3:"qbs_closed3 (exp_qbs_Mx X Y)"
proof(rule qbs_closed3I)
  fix P :: "real \<Rightarrow> nat"
  fix Fi :: "nat \<Rightarrow> real \<Rightarrow> _"
  assume h:"\<And>i. P -` {i} \<in> sets real_borel"
           "\<And>i. Fi i \<in> exp_qbs_Mx X Y"
  show "(\<lambda>r. Fi (P r) r) \<in> exp_qbs_Mx X Y"
    unfolding exp_qbs_Mx_def
  proof(auto intro!: qbs_morphismI)
    fix \<alpha> \<beta>
    assume h':"\<alpha> \<in> pair_qbs_Mx \<real>\<^sub>Q X "
    have 1:"\<And>i. (\<lambda>(r,x). Fi i r x) \<circ> \<alpha> \<in> qbs_Mx Y"
      using qbs_morphismE(3)[OF h(2)[simplified exp_qbs_Mx_def,simplified]] h'
      by(simp add: exp_qbs_Mx_def)
    have 2:"\<And>i. (P \<circ> (\<lambda>r. fst (\<alpha> r)))  -` {i} \<in> sets real_borel"
      using separate_measurable[OF h(1)] h'
      by(auto intro!: measurable_separate simp: pair_qbs_Mx_def comp_def)
    show "(\<lambda>(r, y). Fi (P r) r y) \<circ> \<alpha> \<in> qbs_Mx Y"
      using qbs_closed3_dest[OF 2,of "\<lambda>i. (\<lambda>(r,x). Fi i r x) \<circ> \<alpha>",OF 1]
      by(simp add: comp_def split_beta')
  qed
qed


lemma exp_qbs_correct: "Rep_quasi_borel (exp_qbs X Y) = (X \<rightarrow>\<^sub>Q Y, exp_qbs_Mx X Y)"
  unfolding exp_qbs_def
  by(auto intro!: Abs_quasi_borel_inverse exp_qbs_f simp: exp_qbs_closed1 exp_qbs_closed2 exp_qbs_closed3)

lemma exp_qbs_space[simp]: "qbs_space (exp_qbs X Y) = X \<rightarrow>\<^sub>Q Y"
  by(simp add: qbs_space_def exp_qbs_correct)

lemma exp_qbs_Mx[simp]: "qbs_Mx (exp_qbs X Y) = exp_qbs_Mx X Y"
  by(simp add: qbs_Mx_def exp_qbs_correct)


lemma qbs_exp_morphismI:
  assumes "\<And>\<alpha> \<beta>. \<alpha> \<in> qbs_Mx X \<Longrightarrow>
                 \<beta> \<in> pair_qbs_Mx real_quasi_borel Y \<Longrightarrow>
                 (\<lambda>(r,x). (f \<circ> \<alpha>) r x) \<circ> \<beta> \<in> qbs_Mx Z"
   shows "f \<in> X \<rightarrow>\<^sub>Q exp_qbs Y Z"
  using assms
  by(auto intro!: qbs_morphismI simp: exp_qbs_Mx_def comp_def)

definition qbs_eval :: "(('a \<Rightarrow> 'b) \<times> 'a)  \<Rightarrow> 'b" where
"qbs_eval a \<equiv> (fst a) (snd a)"

lemma qbs_eval_morphism:
  "qbs_eval \<in> (exp_qbs X Y) \<Otimes>\<^sub>Q X \<rightarrow>\<^sub>Q Y"
proof(rule qbs_morphismI,simp)
  fix f
  assume "f \<in> pair_qbs_Mx (exp_qbs X Y) X"
  let ?f1 = "fst \<circ> f"
  let ?f2 = "snd \<circ> f"
  define g :: "real \<Rightarrow> real \<times> _" 
    where "g \<equiv> \<lambda>r.(r,?f2 r)"
  have "g \<in> qbs_Mx (real_quasi_borel \<Otimes>\<^sub>Q X)"
  proof(auto simp add: pair_qbs_Mx_def)
    have "fst \<circ> g = id" by(auto simp add: g_def comp_def)
    thus "fst \<circ> g \<in> real_borel \<rightarrow>\<^sub>M real_borel" by(auto simp add: measurable_ident)
  next
    have "snd \<circ> g = ?f2" by(auto simp add: g_def)
    thus "snd \<circ> g \<in> qbs_Mx X" 
      using \<open>f \<in> pair_qbs_Mx (exp_qbs X Y) X\<close> pair_qbs_Mx_def by auto
  qed
  moreover have "?f1 \<in> exp_qbs_Mx X Y"
    using \<open>f \<in> pair_qbs_Mx (exp_qbs X Y) X\<close>
    by(simp add: pair_qbs_Mx_def)
  ultimately have "(\<lambda>(r,x). (?f1 r x)) \<circ> g \<in> qbs_Mx Y"
    by (auto simp add: exp_qbs_Mx_def qbs_morphism_def)
       (metis (mono_tags, lifting) case_prod_conv comp_apply cond_case_prod_eta)
  moreover have "(\<lambda>(r,x). (?f1 r x)) \<circ> g = qbs_eval \<circ> f" 
    by(auto simp add: case_prod_unfold g_def qbs_eval_def)
  ultimately show "qbs_eval \<circ> f \<in> qbs_Mx Y" by simp
qed

lemma curry_morphism:
 "curry \<in> exp_qbs (X \<Otimes>\<^sub>Q Y) Z \<rightarrow>\<^sub>Q exp_qbs X (exp_qbs Y Z)"
proof(auto intro!: qbs_morphismI simp: exp_qbs_Mx_def)
  fix k \<alpha> \<alpha>'
  assume h:"(\<lambda>(r, xy). k r xy) \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Z"
           "\<alpha> \<in> pair_qbs_Mx \<real>\<^sub>Q X"
           "\<alpha>' \<in> pair_qbs_Mx \<real>\<^sub>Q Y"
  define \<beta> where
   "\<beta> \<equiv> (\<lambda>r. (fst (\<alpha> (fst (\<alpha>' r))),(snd (\<alpha> (fst (\<alpha>' r))), snd (\<alpha>' r))))"
  have "(\<lambda>(x, y). ((\<lambda>(x, y). (curry \<circ> k) x y) \<circ> \<alpha>) x y) \<circ> \<alpha>' = (\<lambda>(r, xy). k r xy) \<circ> \<beta>"
    by(simp add: curry_def split_beta' comp_def \<beta>_def)
  also have "... \<in> qbs_Mx Z"
  proof -
    have "\<beta> \<in> qbs_Mx (\<real>\<^sub>Q \<Otimes>\<^sub>Q X \<Otimes>\<^sub>Q Y)"
      using h(2,3) qbs_closed1_dest[of _ _ "(\<lambda>x. fst (\<alpha>' x))"]
      by(auto simp: pair_qbs_Mx_def \<beta>_def comp_def)
    thus ?thesis
      using h by auto
  qed
  finally show "(\<lambda>(x, y). ((\<lambda>(x, y). (curry \<circ> k) x y) \<circ> \<alpha>) x y) \<circ> \<alpha>' \<in> qbs_Mx Z" .
qed

lemma curry_preserves_morphisms:
  assumes "f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Z"
  shows "curry f \<in> X \<rightarrow>\<^sub>Q exp_qbs Y Z"
  by(rule qbs_morphismE(2)[OF curry_morphism,simplified,OF assms])

lemma uncurry_morphism:
 "case_prod \<in> exp_qbs X (exp_qbs Y Z) \<rightarrow>\<^sub>Q exp_qbs (X \<Otimes>\<^sub>Q Y) Z"
proof(auto intro!: qbs_morphismI simp: exp_qbs_Mx_def)
  fix k \<alpha>
  assume h:"(\<lambda>(x, y). k x y) \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q X \<rightarrow>\<^sub>Q exp_qbs Y Z"
           "\<alpha> \<in> pair_qbs_Mx \<real>\<^sub>Q (X \<Otimes>\<^sub>Q Y)"
  have "(\<lambda>(x, y). (case_prod \<circ> k) x y) \<circ> \<alpha> = (\<lambda>(r,y). k (fst (\<alpha> r)) (fst (snd (\<alpha> r))) y) \<circ> (\<lambda>r. (r,snd (snd (\<alpha> r))))"
    by(simp add: split_beta' comp_def)
  also have "... \<in> qbs_Mx Z"
  proof(rule qbs_morphismE(3)[where X="\<real>\<^sub>Q \<Otimes>\<^sub>Q Y"])
    have "(\<lambda>r. k (fst (\<alpha> r)) (fst (snd (\<alpha> r)))) = (\<lambda>(x, y). k x y) \<circ> (\<lambda>r. (fst (\<alpha> r),fst (snd (\<alpha> r))))"
      by auto
    also have "... \<in> qbs_Mx (exp_qbs Y Z)"
      apply(rule qbs_morphismE(3)[where X="\<real>\<^sub>Q \<Otimes>\<^sub>Q X"])
      using h(2) by(auto simp: h(1) pair_qbs_Mx_def comp_def)
    finally show " (\<lambda>(r, y). k (fst (\<alpha> r)) (fst (snd (\<alpha> r))) y) \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Z"
      by(simp add: exp_qbs_Mx_def)
  next
    show "(\<lambda>r. (r, snd (snd (\<alpha> r)))) \<in> qbs_Mx (\<real>\<^sub>Q \<Otimes>\<^sub>Q Y)"
      using h(2) by(simp add: pair_qbs_Mx_def comp_def)
  qed
  finally show "(\<lambda>(x, y). (case_prod \<circ> k) x y) \<circ> \<alpha> \<in> qbs_Mx Z" .
qed

lemma uncurry_preserves_morphisms:
  assumes "f \<in> X \<rightarrow>\<^sub>Q exp_qbs Y Z"
  shows "case_prod f \<in> X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Z"
 by(rule qbs_morphismE(2)[OF uncurry_morphism,simplified,OF assms])

lemma arg_swap_morphism:
  assumes "f \<in> X \<rightarrow>\<^sub>Q exp_qbs Y Z"
  shows "(\<lambda>y x. f x y) \<in> Y \<rightarrow>\<^sub>Q exp_qbs X Z"
  using curry_preserves_morphisms[OF qbs_morphism_pair_swap[OF uncurry_preserves_morphisms[OF assms]]]
  by simp

lemma exp_qbs_comp_morphism:
  assumes "f \<in> W \<rightarrow>\<^sub>Q exp_qbs X Y"
      and "g \<in> W \<rightarrow>\<^sub>Q exp_qbs Y Z"
    shows "(\<lambda>w. g w \<circ> f w) \<in> W \<rightarrow>\<^sub>Q exp_qbs X Z"
proof(rule qbs_exp_morphismI)
  fix \<alpha> \<beta>
  assume h: "\<alpha> \<in> qbs_Mx W"
            "\<beta> \<in> pair_qbs_Mx \<real>\<^sub>Q X"
  have "(\<lambda>(r, x). ((\<lambda>w. g w \<circ> f w) \<circ> \<alpha>) r x) \<circ> \<beta>= case_prod g \<circ> (\<lambda>r. ((\<alpha> \<circ> (fst \<circ> \<beta>)) r, case_prod f ((\<alpha> \<circ> (fst \<circ> \<beta>)) r, (snd \<circ> \<beta>) r)))"
    by(simp add: split_beta' comp_def)
  also have "... \<in> qbs_Mx Z"
  proof -
    have "(\<lambda>r. ((\<alpha> \<circ> (fst \<circ> \<beta>)) r, case_prod f ((\<alpha> \<circ> (fst \<circ> \<beta>)) r, (snd \<circ> \<beta>) r))) \<in> qbs_Mx (W \<Otimes>\<^sub>Q Y)"
    proof(auto simp add: pair_qbs_Mx_def)
      have "fst \<circ> (\<lambda>r. (\<alpha> (fst (\<beta> r)), f (\<alpha> (fst (\<beta> r))) (snd (\<beta> r)))) = \<alpha> \<circ> (fst \<circ> \<beta>)"
        by (simp add: comp_def)
      also have "... \<in> qbs_Mx W"
        using qbs_decomp[of W] h
        by(simp add: pair_qbs_Mx_def qbs_closed1_def)
      finally show "fst \<circ> (\<lambda>r. (\<alpha> (fst (\<beta> r)), f (\<alpha> (fst (\<beta> r))) (snd (\<beta> r)))) \<in> qbs_Mx W" .
    next
      have [simp]:"snd \<circ> (\<lambda>r. (\<alpha> (fst (\<beta> r)), f (\<alpha> (fst (\<beta> r))) (snd (\<beta> r)))) =  case_prod f \<circ> (\<lambda>r. ((\<alpha> \<circ> (fst \<circ> \<beta>)) r, (snd \<circ> \<beta>) r))"
        by(simp add: comp_def)
      have "(\<lambda>r. ((\<alpha> \<circ> (fst \<circ> \<beta>)) r, (snd \<circ> \<beta>) r)) \<in> qbs_Mx (W \<Otimes>\<^sub>Q X)"
      proof(auto simp add: pair_qbs_Mx_def)
        have "fst \<circ> (\<lambda>r. (\<alpha> (fst (\<beta> r)), snd (\<beta> r)))= \<alpha> \<circ> (fst \<circ> \<beta>)"
          by (simp add: comp_def)
        also have "... \<in> qbs_Mx W"
          using qbs_decomp[of W] h
          by(simp add: pair_qbs_Mx_def qbs_closed1_def)
        finally show "fst \<circ> (\<lambda>r. (\<alpha> (fst (\<beta> r)), snd (\<beta> r))) \<in> qbs_Mx W" .
      next
        show "snd \<circ> (\<lambda>r. (\<alpha> (fst (\<beta> r)), snd (\<beta> r))) \<in> qbs_Mx X"
          using h
          by(simp add: pair_qbs_Mx_def comp_def)
      qed
      hence "case_prod f \<circ> (\<lambda>r. ((\<alpha> \<circ> (fst \<circ> \<beta>)) r, (snd \<circ> \<beta>) r)) \<in> qbs_Mx Y"
        using uncurry_preserves_morphisms[OF assms(1)] by auto
      thus "snd \<circ> (\<lambda>r. (\<alpha> (fst (\<beta> r)), f (\<alpha> (fst (\<beta> r))) (snd (\<beta> r)))) \<in> qbs_Mx Y"
        by simp
    qed
    thus ?thesis
      using uncurry_preserves_morphisms[OF assms(2)]
      by auto
  qed
  finally show "(\<lambda>(r, x). ((\<lambda>w. g w \<circ> f w) \<circ> \<alpha>) r x) \<circ> \<beta> \<in> qbs_Mx Z" .
qed

lemma case_sum_morphism:
 "case_prod case_sum \<in> exp_qbs X Z \<Otimes>\<^sub>Q exp_qbs Y Z  \<rightarrow>\<^sub>Q exp_qbs (X <+>\<^sub>Q Y) Z"
proof(rule qbs_exp_morphismI)
  fix \<alpha> \<beta>
  assume h0:"\<alpha> \<in> qbs_Mx (exp_qbs X Z \<Otimes>\<^sub>Q exp_qbs Y Z)"
            "\<beta> \<in> pair_qbs_Mx \<real>\<^sub>Q (X <+>\<^sub>Q Y)"
  let ?\<alpha>1 = "fst \<circ> \<alpha>"
  let ?\<alpha>2 = "snd \<circ> \<alpha>"
  let ?\<beta>1 = "fst \<circ> \<beta>"
  let ?\<beta>2 = "snd \<circ> \<beta>"
  have h:"?\<alpha>1 \<in> exp_qbs_Mx X Z"
         "?\<alpha>2 \<in> exp_qbs_Mx Y Z"
         "?\<beta>1 \<in> real_borel \<rightarrow>\<^sub>M real_borel"
         "?\<beta>2 \<in> copair_qbs_Mx X Y"
    using h0 by (auto simp add: pair_qbs_Mx_def)
  hence "\<exists>S\<in>sets real_borel. (S = {} \<longrightarrow> (\<exists>\<alpha>1\<in>qbs_Mx X. ?\<beta>2 = (\<lambda>r. Inl (\<alpha>1 r)))) \<and>
                             (S = UNIV \<longrightarrow> (\<exists>\<alpha>2\<in>qbs_Mx Y. ?\<beta>2 = (\<lambda>r. Inr (\<alpha>2 r)))) \<and>
                             (S \<noteq> {} \<and> S \<noteq> UNIV \<longrightarrow>
                            (\<exists>\<alpha>1\<in>qbs_Mx X. \<exists>\<alpha>2\<in>qbs_Mx Y. ?\<beta>2 = (\<lambda>r. if r \<in> S then Inl (\<alpha>1 r) else Inr (\<alpha>2 r))))"
    by(simp add: copair_qbs_Mx_def)
  then obtain S :: "real set" where hs:
   "S\<in>sets real_borel \<and> (S = {} \<longrightarrow> (\<exists>\<alpha>1\<in>qbs_Mx X. ?\<beta>2 = (\<lambda>r. Inl (\<alpha>1 r)))) \<and>
                         (S = UNIV \<longrightarrow> (\<exists>\<alpha>2\<in>qbs_Mx Y. ?\<beta>2 = (\<lambda>r. Inr (\<alpha>2 r)))) \<and>
                         (S \<noteq> {} \<and> S \<noteq> UNIV \<longrightarrow>
                          (\<exists>\<alpha>1\<in>qbs_Mx X. \<exists>\<alpha>2\<in>qbs_Mx Y. ?\<beta>2 = (\<lambda>r. if r \<in> S then Inl (\<alpha>1 r) else Inr (\<alpha>2 r))))"
    by auto
  show "(\<lambda>(r, x). ((\<lambda>(x, y). case_sum x y) \<circ> \<alpha>) r x) \<circ> \<beta> \<in> qbs_Mx Z"
  proof -
    have "(\<lambda>(r, x). ((\<lambda>(x, y). case_sum x y) \<circ> \<alpha>) r x) \<circ> \<beta> = (\<lambda>r. case_sum (?\<alpha>1 (?\<beta>1 r)) (?\<alpha>2 (?\<beta>1 r)) (?\<beta>2 r))"
          (is "?lhs = ?rhs")
      by(auto simp: split_beta' comp_def) (metis comp_apply)
    also have "... \<in> qbs_Mx Z"
         (is "?f \<in> _")
    proof -
      consider "S = {}" | "S = UNIV" | "S \<noteq> {} \<and> S \<noteq> UNIV" by auto
      then show ?thesis
      proof cases
        case 1
        then obtain \<alpha>1 where h1:
         "\<alpha>1\<in>qbs_Mx X \<and> ?\<beta>2 = (\<lambda>r. Inl (\<alpha>1 r))"
          using hs by auto
        then have "(\<lambda>r. case_sum (?\<alpha>1 (?\<beta>1 r)) (?\<alpha>2 (?\<beta>1 r)) (?\<beta>2 r)) = (\<lambda>r. ?\<alpha>1 (?\<beta>1 r) (\<alpha>1 r))"
          by simp
        also have "... = case_prod ?\<alpha>1 \<circ> (\<lambda>r. (?\<beta>1 r,\<alpha>1 r))"
          by auto
        also have "... \<in> \<real>\<^sub>Q \<rightarrow>\<^sub>Q Z"
          apply(rule qbs_morphism_comp[of _ _ "\<real>\<^sub>Q \<Otimes>\<^sub>Q X"])
           apply(rule qbs_morphism_tuple)
          using h(3)
            apply blast
          using qbs_Mx_is_morphisms h1
           apply blast
          using qbs_Mx_is_morphisms[of "\<real>\<^sub>Q \<Otimes>\<^sub>Q X"] h(1)
          by (simp add: exp_qbs_Mx_def)
        finally show ?thesis
          using qbs_Mx_is_morphisms by auto
      next
        case 2
        then obtain \<alpha>2 where h2:
         "\<alpha>2\<in>qbs_Mx Y \<and> ?\<beta>2 = (\<lambda>r. Inr (\<alpha>2 r))"
          using hs by auto
        then have "(\<lambda>r. case_sum (?\<alpha>1 (?\<beta>1 r)) (?\<alpha>2 (?\<beta>1 r)) (?\<beta>2 r)) = (\<lambda>r. ?\<alpha>2 (?\<beta>1 r) (\<alpha>2 r))"
          by simp
        also have "... = case_prod ?\<alpha>2 \<circ> (\<lambda>r. (?\<beta>1 r,\<alpha>2 r))"
          by auto
        also have "... \<in> \<real>\<^sub>Q \<rightarrow>\<^sub>Q Z"
          apply(rule qbs_morphism_comp[of _ _ "\<real>\<^sub>Q \<Otimes>\<^sub>Q Y"])
           apply(rule qbs_morphism_tuple)
          using h(3)
            apply blast
          using qbs_Mx_is_morphisms h2
           apply blast
          using qbs_Mx_is_morphisms[of "\<real>\<^sub>Q \<Otimes>\<^sub>Q Y"] h(2)
          by (simp add: exp_qbs_Mx_def)
        finally show ?thesis
          using qbs_Mx_is_morphisms by auto
      next
        case 3
        then obtain \<alpha>1 \<alpha>2 where h3:
          "\<alpha>1\<in>qbs_Mx X \<and> \<alpha>2\<in>qbs_Mx Y \<and> ?\<beta>2 = (\<lambda>r. if r \<in> S then Inl (\<alpha>1 r) else Inr (\<alpha>2 r))"
          using hs by auto
        define P :: "real \<Rightarrow> nat"
          where "P \<equiv> (\<lambda>r. if r \<in> S then 0 else 1)"
        define \<gamma> :: "nat \<Rightarrow> real \<Rightarrow> _"
          where "\<gamma> \<equiv> (\<lambda>n r. if n = 0 then ?\<alpha>1 (?\<beta>1 r) (\<alpha>1 r) else ?\<alpha>2 (?\<beta>1 r) (\<alpha>2 r))"
        then have "(\<lambda>r. case_sum (?\<alpha>1 (?\<beta>1 r)) (?\<alpha>2 (?\<beta>1 r)) (?\<beta>2 r)) =(\<lambda>r. \<gamma> (P r) r)"
          by(auto simp add: P_def \<gamma>_def h3)
        also have "... \<in> qbs_Mx Z"
        proof -
          have "\<forall>i. P -` {i} \<in> sets real_borel"
            using hs borel_comp[of S] by(simp add: P_def)
          moreover have"\<forall>i. \<gamma> i \<in> qbs_Mx Z"
          proof
            fix i :: nat
            consider "i = 0" | "i \<noteq> 0" by auto
            then show "\<gamma> i \<in> qbs_Mx Z"
            proof cases
              case 1
              then have "\<gamma> i = (\<lambda>r. ?\<alpha>1 (?\<beta>1 r) (\<alpha>1 r))"
                by(simp add: \<gamma>_def)
              also have "... = case_prod ?\<alpha>1 \<circ> (\<lambda>r. (?\<beta>1 r,\<alpha>1 r))"
                by auto
              also have "... \<in> \<real>\<^sub>Q \<rightarrow>\<^sub>Q Z"
                apply(rule qbs_morphism_comp[of _ _ "\<real>\<^sub>Q \<Otimes>\<^sub>Q X"])
                 apply(rule qbs_morphism_tuple)
                using h(3)
                  apply blast
                using qbs_Mx_is_morphisms h3
                 apply blast
                using qbs_Mx_is_morphisms[of "\<real>\<^sub>Q \<Otimes>\<^sub>Q X"] h(1)
                by (simp add: exp_qbs_Mx_def)
              finally show ?thesis
                using qbs_Mx_is_morphisms by auto
            next
              case 2
              then have "\<gamma> i = (\<lambda>r. ?\<alpha>2 (?\<beta>1 r) (\<alpha>2 r))"
                by(simp add: \<gamma>_def)
              also have "... = case_prod ?\<alpha>2 \<circ> (\<lambda>r. (?\<beta>1 r,\<alpha>2 r))"
                by auto
              also have "... \<in> \<real>\<^sub>Q \<rightarrow>\<^sub>Q Z"
                apply(rule qbs_morphism_comp[of _ _ "\<real>\<^sub>Q \<Otimes>\<^sub>Q Y"])
                 apply(rule qbs_morphism_tuple)
                using h(3)
                  apply blast
                using qbs_Mx_is_morphisms h3
                 apply blast
                using qbs_Mx_is_morphisms[of "\<real>\<^sub>Q \<Otimes>\<^sub>Q Y"] h(2)
                by (simp add: exp_qbs_Mx_def)
              finally show ?thesis
                using qbs_Mx_is_morphisms by auto
            qed
          qed
          ultimately show ?thesis
            using qbs_decomp[of Z]
            by(simp add: qbs_closed3_def)
        qed
        finally show ?thesis .
      qed
    qed
    finally show ?thesis .
  qed
qed


lemma not_qbs_morphism:
 "Not \<in> \<bool>\<^sub>Q \<rightarrow>\<^sub>Q \<bool>\<^sub>Q"
  by(auto intro!: bool_qbs_morphism)

lemma or_qbs_morphism:
 "(\<or>) \<in> \<bool>\<^sub>Q \<rightarrow>\<^sub>Q exp_qbs \<bool>\<^sub>Q \<bool>\<^sub>Q"
  by(auto intro!: bool_qbs_morphism)

lemma and_qbs_morphism:
 "(\<and>) \<in> \<bool>\<^sub>Q \<rightarrow>\<^sub>Q exp_qbs \<bool>\<^sub>Q \<bool>\<^sub>Q"
  by(auto intro!: bool_qbs_morphism)

lemma implies_qbs_morphism:
 "(\<longrightarrow>) \<in> \<bool>\<^sub>Q \<rightarrow>\<^sub>Q \<bool>\<^sub>Q \<Rightarrow>\<^sub>Q \<bool>\<^sub>Q"
  by(auto intro!: bool_qbs_morphism)


lemma less_nat_qbs_morphism:
 "(<) \<in> \<nat>\<^sub>Q \<rightarrow>\<^sub>Q exp_qbs \<nat>\<^sub>Q \<bool>\<^sub>Q"
  by(auto intro!: nat_qbs_morphism)

lemma less_real_qbs_morphism:
 "(<) \<in> \<real>\<^sub>Q \<rightarrow>\<^sub>Q exp_qbs \<real>\<^sub>Q \<bool>\<^sub>Q"
proof(rule curry_preserves_morphisms[where f="(\<lambda>(z :: real \<times> real). fst z < snd z)",simplified curry_def,simplified])
  have "(\<lambda>z. fst z < snd z) \<in> real_borel \<Otimes>\<^sub>M real_borel \<rightarrow>\<^sub>M bool_borel"
    using borel_measurable_pred_less[OF measurable_fst measurable_snd,simplified measurable_cong_sets[OF refl sets_borel_eq_count_space[symmetric],of "borel \<Otimes>\<^sub>M borel"]]
    by simp
  thus "(\<lambda>z. fst z < snd z) \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q \<real>\<^sub>Q \<rightarrow>\<^sub>Q \<bool>\<^sub>Q"
    by auto
qed


lemma rec_list_morphism':
 "rec_list' \<in> qbs_space (exp_qbs Y (exp_qbs (exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y))) (exp_qbs (list_of X) Y)))"
  apply(simp,rule curry_preserves_morphisms[where f="\<lambda>yf. rec_list' (fst yf) (snd yf)",simplified curry_def, simplified])
  apply(rule arg_swap_morphism)
proof(rule coprod_qbs_canonical1')
  fix n
  show "(\<lambda>x y. rec_list' (fst y) (snd y) (n, x)) \<in> (\<Pi>\<^sub>Q i\<in>{..<n}. X) \<rightarrow>\<^sub>Q exp_qbs (Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y))) Y"
  proof(induction n)
    case 0
    show ?case
    proof(rule curry_preserves_morphisms[of " (\<lambda>(x,y). rec_list' (fst y) (snd y) (0, x))", simplified],rule qbs_morphismI)
      fix \<alpha>
      assume h:"\<alpha> \<in> qbs_Mx ((\<Pi>\<^sub>Q i\<in>{..<0::nat}. X) \<Otimes>\<^sub>Q Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y)))"
      have "\<And>r. fst (\<alpha> r) = (\<lambda>n. undefined)"
      proof -
        fix r
        have "\<And>i. (\<lambda>r. fst (\<alpha> r) i) = (\<lambda>r. undefined)"
          using h by(auto simp: exp_qbs_Mx_def prod_qbs_Mx_def pair_qbs_Mx_def comp_def split_beta')
        thus "fst (\<alpha> r) = (\<lambda>n. undefined)"
          by(fastforce dest: fun_cong)
      qed
      hence "(\<lambda>(x, y). rec_list' (fst y) (snd y) (0, x)) \<circ> \<alpha> = (\<lambda>x. fst (snd (\<alpha> x)))"
        by(auto simp: rec_list'_simp1 comp_def split_beta')
      also have "... \<in> qbs_Mx Y"
        using h by(auto simp: pair_qbs_Mx_def comp_def)
      finally show "(\<lambda>(x, y). rec_list' (fst y) (snd y) (0, x)) \<circ> \<alpha> \<in> qbs_Mx Y" .
    qed
  next
    case ih:(Suc n)
    show ?case
    proof(rule qbs_morphismI)
      fix \<alpha>
      assume h:"\<alpha> \<in> qbs_Mx (\<Pi>\<^sub>Q i\<in>{..<Suc n}. X)"
      define \<alpha>' where "\<alpha>' \<equiv> (\<lambda>r. snd (list_tail (Suc n, \<alpha> r)))"
      define a where "a \<equiv> (\<lambda>r. \<alpha> r 0)"
      then have ha:"a \<in> qbs_Mx X"
        using h by(auto simp: prod_qbs_Mx_def)
      have 1:"\<alpha>' \<in> qbs_Mx (\<Pi>\<^sub>Q i\<in>{..<n}. X)"
        using h by(fastforce simp: prod_qbs_Mx_def list_tail_def \<alpha>'_def)
      hence 2: "\<And>r. (n, \<alpha>' r) \<in> qbs_space (list_of X)"
        using qbs_Mx_to_X[of \<alpha>'] by fastforce
      have 3: "\<And>r. (Suc n, \<alpha> r) \<in> qbs_space (list_of X)"
        using qbs_Mx_to_X[of \<alpha>] h by fastforce
      have 4: "\<And>r. (n, \<alpha>' r) = list_tail (Suc n, \<alpha> r)"
        by(simp add: list_tail_def \<alpha>'_def)
      have 5: "\<And>r. (Suc n, \<alpha> r) = list_cons (a r) (n, \<alpha>' r)"
        unfolding a_def by(simp add: list_simp5[OF 3,simplified 4[symmetric],simplified list_head_def]) auto
      have 6: "(\<lambda>r. (n, \<alpha>' r)) \<in> qbs_Mx (list_of X)"
        using 1 by(auto intro!: coprod_qbs_MxI)

      have "(\<lambda>x y. rec_list' (fst y) (snd y) (Suc n, x)) \<circ> \<alpha> = (\<lambda>r y. rec_list' (fst y) (snd y) (Suc n, \<alpha> r))"
        by auto
      also have "... = (\<lambda>r y. snd y (a r) (n, \<alpha>' r) (rec_list' (fst y) (snd y) (n, \<alpha>' r)))"
        by(simp only: 5 rec_list'_simp2[OF 2])
      also have "... \<in> qbs_Mx (exp_qbs (Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y))) Y)"
      proof -
        have "(\<lambda>(r,y). snd y (a r) (n, \<alpha>' r) (rec_list' (fst y) (snd y) (n, \<alpha>' r))) = (\<lambda>(y,x1,x2,x3). y x1 x2 x3) \<circ> (\<lambda>(r,y). (snd y, a r, (n, \<alpha>' r), rec_list' (fst y) (snd y) (n, \<alpha>' r)))"
          by auto
        also have "... \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q (Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y))) \<rightarrow>\<^sub>Q Y"
        proof(rule qbs_morphism_comp[where Y="exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y)) \<Otimes>\<^sub>Q X \<Otimes>\<^sub>Q list_of X \<Otimes>\<^sub>Q Y"])
          show "(\<lambda>(r, y). (snd y, a r, (n, \<alpha>' r), rec_list' (fst y) (snd y) (n, \<alpha>' r))) \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y)) \<rightarrow>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y)) \<Otimes>\<^sub>Q X \<Otimes>\<^sub>Q list_of X \<Otimes>\<^sub>Q Y"
          proof(auto simp: split_beta' intro!: qbs_morphism_tuple[OF qbs_morphism_snd''[OF snd_qbs_morphism] qbs_morphism_tuple[of "\<lambda>(r, y). a r" "\<real>\<^sub>Q \<Otimes>\<^sub>Q Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y))" X], OF _ qbs_morphism_tuple[of "\<lambda>(r,y).  (n, \<alpha>' r)"],of "list_of X" "\<lambda>(r,y). rec_list' (fst y) (snd y) (n, \<alpha>' r)",simplified split_beta'])
            show "(\<lambda>x. a (fst x)) \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y)) \<rightarrow>\<^sub>Q X"
              using ha qbs_Mx_is_morphisms[of X] qbs_morphism_fst''[of a "\<real>\<^sub>Q" X] by auto
          next
            show "(\<lambda>x. (n, \<alpha>' (fst x))) \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y)) \<rightarrow>\<^sub>Q list_of X"
              using qbs_morphism_fst''[of "\<lambda>r. (n, \<alpha>' r)" "\<real>\<^sub>Q" "list_of X"] qbs_Mx_is_morphisms[of "list_of X"] 6 by auto
          next
            show "(\<lambda>x. rec_list' (fst (snd x)) (snd (snd x)) (n, \<alpha>' (fst x))) \<in> \<real>\<^sub>Q \<Otimes>\<^sub>Q Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y)) \<rightarrow>\<^sub>Q Y"
              using qbs_morphismE(3)[OF ih 1, simplified comp_def]  uncurry_preserves_morphisms[of "(\<lambda>x y. rec_list' (fst y) (snd y) (n, \<alpha>' x))" "\<real>\<^sub>Q" "Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y))" Y] qbs_Mx_is_morphisms[of "exp_qbs (Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y))) Y"]
              by(fastforce simp: split_beta')
          qed
        next
          show "(\<lambda>(y, x1, x2, x3). y x1 x2 x3) \<in> exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y)) \<Otimes>\<^sub>Q X \<Otimes>\<^sub>Q list_of X \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Y"
          proof(rule qbs_morphismI)
            fix \<beta>
            assume "\<beta> \<in> qbs_Mx (exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y)) \<Otimes>\<^sub>Q X \<Otimes>\<^sub>Q list_of X \<Otimes>\<^sub>Q Y)"
            then have "\<exists> \<beta>1 \<beta>2 \<beta>3 \<beta>4. \<beta> = (\<lambda>r. (\<beta>1 r, \<beta>2 r, \<beta>3 r, \<beta>4 r)) \<and> \<beta>1 \<in> qbs_Mx (exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y))) \<and> \<beta>2 \<in> qbs_Mx X \<and> \<beta>3 \<in> qbs_Mx (list_of X) \<and> \<beta>4 \<in> qbs_Mx Y"
              by(auto intro!: exI[where x="fst \<circ> \<beta>"] exI[where x="fst \<circ> snd \<circ> \<beta>"] exI[where x="fst \<circ> snd \<circ> snd \<circ> \<beta>"] exI[where x="snd \<circ> snd \<circ> snd \<circ> \<beta>"] simp:pair_qbs_Mx_def comp_def) 
            then obtain \<beta>1 \<beta>2 \<beta>3 \<beta>4 where hb:
             "\<beta> = (\<lambda>r. (\<beta>1 r, \<beta>2 r, \<beta>3 r, \<beta>4 r))" "\<beta>1 \<in> qbs_Mx (exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y)))" "\<beta>2 \<in> qbs_Mx X" "\<beta>3 \<in> qbs_Mx (list_of X)" "\<beta>4 \<in> qbs_Mx Y"
              by auto
            hence hbq:"(\<lambda>(((r,x1),x2),x3). \<beta>1 r x1 x2 x3) \<in> ((\<real>\<^sub>Q \<Otimes>\<^sub>Q X) \<Otimes>\<^sub>Q list_of X) \<Otimes>\<^sub>Q Y \<rightarrow>\<^sub>Q Y"
              by(simp add: exp_qbs_Mx_def) (meson uncurry_preserves_morphisms)
            have "(\<lambda>(y, x1, x2, x3). y x1 x2 x3) \<circ> \<beta> = (\<lambda>(((r,x1),x2),x3). \<beta>1 r x1 x2 x3) \<circ> (\<lambda>r. (((r,\<beta>2 r), \<beta>3 r), \<beta>4 r))"
              by(auto simp: hb(1))
            also have "... \<in> \<real>\<^sub>Q \<rightarrow>\<^sub>Q Y"
              using hb(2-5)
              by(auto intro!: qbs_morphism_comp[OF qbs_morphism_tuple[OF qbs_morphism_tuple[OF qbs_morphism_tuple[OF qbs_morphism_ident']]] hbq] simp: qbs_Mx_is_morphisms)
            finally show "(\<lambda>(y, x1, x2, x3). y x1 x2 x3) \<circ> \<beta> \<in> qbs_Mx Y"
              by(simp add: qbs_Mx_is_morphisms)
          qed
        qed
        finally show ?thesis
          by(simp add: exp_qbs_Mx_def)
      qed
      finally show "(\<lambda>x y. rec_list' (fst y) (snd y) (Suc n, x)) \<circ> \<alpha> \<in> qbs_Mx (exp_qbs (Y \<Otimes>\<^sub>Q exp_qbs X (exp_qbs (list_of X) (exp_qbs Y Y))) Y)" .
    qed
  qed
qed simp


end