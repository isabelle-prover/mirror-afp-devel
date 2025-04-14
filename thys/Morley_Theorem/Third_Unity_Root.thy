theory Third_Unity_Root

imports Complex_Angles

begin

section \<open>Third unity root\<close>

text \<open>In this section we prove some basic properties of the third unity root j.\<close>

lemma root_unity_3: \<open>(z::complex)^3 - 1 = 0 \<longleftrightarrow> (z = cis (2*pi/3) \<or> z=1 \<or> z = cis (4*pi/3))\<close>
proof(rule iffI) 
  have \<open>cis (2 * pi * real xa / 3) \<noteq> 1 \<Longrightarrow>
          cis (2 * pi * real xa / 3) \<noteq> cis (2 * pi / 3) 
  \<Longrightarrow> xa < 3 \<Longrightarrow> cis (2 * pi * real xa / 3) = cis (4 * pi / 3) \<close>
    for xa
  proof(rule ccontr) 
    assume h:\<open>cis (2 * pi * real xa / 3) \<noteq> 1\<close>
      \<open>cis (2 * pi * real xa / 3) \<noteq> cis (2 * pi / 3)\<close>
      \<open>xa < 3\<close> \<open>cis (2 * pi * real xa / 3) \<noteq> cis (4 * pi / 3)\<close>
    then have \<open>xa = 1 \<or> xa = 0\<close> 
      using less_Suc_eq numeral_3_eq_3 by fastforce
    then show False 
      using h(1) h(2) by auto
  qed
  then have f0:\<open>(\<lambda>k. cis (2 * pi * real k / real 3)) ` {..<3} = {1, cis(2*pi/3), cis (4*pi/3)}\<close>
    unfolding image_def  by(auto simp: image_def intro:bexI[where x=0] 
        bexI[where x=1] bexI[where x=2])  
  have \<open>{z. z^3 = 1} = {1, cis(2*pi/3), cis (4*pi/3)}\<close>
    apply(insert bij_betw_roots_unity[of 3, simplified]) 
    apply(frule bij_betw_imp_surj_on) 
    using f0 by auto
  then show \<open>z ^ 3 - 1 = 0 \<Longrightarrow> z = cis (2 * pi / 3) \<or> z = 1 \<or> z = cis (4 * pi / 3)\<close>
    unfolding bij_betw_def inj_on_def by(auto) 
  show \<open> z = cis (2 * pi / 3) \<or> z = 1 \<or> z = cis (4 * pi / 3) \<Longrightarrow> z ^ 3 - 1 = 0 \<close>
    using cis_2pi cis_multiple_2pi[of 2] by(auto simp:DeMoivre field_simps) 
qed

definition root3 where \<open>root3\<equiv>cis(2*pi/3)\<close>

lemma root3_eq_0:\<open>1 + root3 + root3^2 = 0\<close>
proof -
  have \<open>(z::complex)^3 - 1 = (z - 1)*(1 + z + z^2)\<close> for z
    by(auto simp:field_simps power2_eq_square power3_eq_cube) 
  moreover have \<open>root3^3 - 1 = 0\<close>
    using root_unity_3 unfolding root3_def by blast
  moreover have \<open>root3-1 \<noteq> 0\<close> 
    by(simp add:cis.code Complex_eq_1 cos_120 root3_def)
  ultimately show ?thesis 
    by simp
qed    

lemma root_unity_carac:
  assumes h1:\<open>a1*a2*a3 = j\<close> \<open>1-a1*a2 \<noteq> 0 \<and> 1-a2*a3\<noteq>0 \<and> 1-a1*a3 \<noteq> 0\<close> \<open>j=root3\<close>
    and  R : \<open>R=(a1 * b2 + b1) / (1 - a1 * a2)\<close> (is \<open>R=?R\<close>)
    and P :\<open>P=(a2*b3 + b2)/(1-a2*a3)\<close> (is \<open>P=?P\<close>)
    and Q:\<open>Q=(a3*b1 + b3)/(1-a3*a1)\<close> (is \<open>Q=?Q\<close>)
  shows \<open>(a1^2+a1+1)*b1 + a1^3*(a2^2+a2+1)*b2 +a1^3*a2^3*(a3^2+a3+1)*b3 =
      -j*a1^2*a2*(a1-j)*(a2-j)*(a3-j)*(?R +j*?P +j^2*?Q)\<close>
proof -
  have simp_rules_for_eq:\<open>1-a1*a2 \<noteq> 0 \<and> 1-a2*a3\<noteq>0 \<and> 1-a1*a3 \<noteq> 0\<close> \<open>a1*a2*a3 = j\<close>
    \<open>1 + j +j^2 = 0\<close> \<open>j*j*j = 1\<close> \<open>(1-a1*a2)*a3 = (a3-j)\<close> \<open>(1-a2*a3)*a1 = (a1-j)\<close> \<open>(1-a1*a3)*a2 = (a2-j)\<close>
    using h1 root3_eq_0 root_unity_3 unfolding root3_def
    by(auto simp:power3_eq_cube mult.left_commute   mult.commute right_diff_distrib) 
  have y:\<open> (- j * a1\<^sup>2 * a2 * ((1 - a2 * a3) * a1) * ((1 - a1 * a3) * a2) * ((1 - a1 * a2) * a3) *
   (a1 * b2) + - j * a1\<^sup>2 * a2 * ((1 - a2 * a3) * a1) * ((1 - a1 * a3) * a2) * ((1 - a1 * a2) * a3) * b1) /
    (1 - a1 * a2) = (- j * a1\<^sup>2 * a2 * ((1 - a3 * a2) * a1) * ((1 - a1 * a3) * a2) * ( a3) * (a1 * b2)
    + - j * a1\<^sup>2 * a2 * ((1 - a3 * a2) * a1) * ((1 - a1 * a3) * a2) * (a3) * b1)\<close>
    apply(subst add_divide_distrib) 
    using simp_rules_for_eq(1) 
    by (simp add: mult.commute)
  have y2:\<open>(- j * a1\<^sup>2 * a2 * ((1 - a2 * a3) * a1) * ((1 - a1 * a3) * a2) * ((1 - a1 * a2) * a3) * (j * (a2 * b3)) +
     - j * a1\<^sup>2 * a2 * ((1 - a2 * a3) * a1) * ((1 - a1 * a3) * a2) * ((1 - a1 * a2) * a3) * (j * b2)) /
    (1 - a2 * a3) = (- j * a1\<^sup>2 * a2 * (a1) * ((1 - a1 * a3) * a2) * ((1 - a1 * a2) * a3) * (j * (a2 * b3)) +
     - j * a1\<^sup>2 * a2 * (a1) * ((1 - a1 * a3) * a2) * ((1 - a1 * a2) * a3) * (j * b2))\<close>
    apply(subst add_divide_distrib) 
    using simp_rules_for_eq(1) by auto
  have y3:\<open>(- j * a1\<^sup>2 * a2 * ((1 - a2 * a3) * a1) * ((1 - a1 * a3) * a2) * ((1 - a1 * a2) * a3) * (j\<^sup>2 * (a3 * b1)) +
     - j * a1\<^sup>2 * a2 * ((1 - a2 * a3) * a1) * ((1 - a1 * a3) * a2) * ((1 - a1 * a2) * a3) * (j\<^sup>2 * b3)) /
    (1 - a3 * a1) =
(- j * a1\<^sup>2 * a2 * ((1 - a2 * a3) * a1) * (a2) * ((1 - a1 * a2) * a3) * (j\<^sup>2 * (a3 * b1)) +
     - j * a1\<^sup>2 * a2 * ((1 - a2 * a3) * a1) * (a2) * ((1 - a1 * a2) * a3) * (j\<^sup>2 * b3))\<close>
    apply(subst add_divide_distrib) 
    by (smt (verit, best) mult.commute nonzero_mult_div_cancel_left times_divide_eq_left simp_rules_for_eq(1))
  have ko:\<open>a*(b*(c)) = a*b*c\<close> for a b c::complex
    by auto
  have ko':\<open>a +(b +(c)) = a+b+c\<close> for a b c::complex
    by auto
  have *:\<open>a1 * a1 * a1 * a1 * a1 * a2 * a2 * a2 * a2 * a3 * a3 * a3 * a3 * b1 = a1*a1*a2*a3*b1\<close>
    using simp_rules_for_eq by (auto simp add: mult.assoc mult.left_commute)
  have **:\<open>a1 * a1 * a1 * a1 * a1 * a2 * a2 * a2 * a2 * a2 * a3 * a3 * a3 * b3 = a1*a1*a2*a2*b3\<close>
    using simp_rules_for_eq by (auto simp add: mult.assoc mult.left_commute)
  have ***:\<open>a1 * a1 * a1 * a1 * a1 * a1 * a2 * a2 * a2 * a2 * a2 * a3 * a3 * a3 * a3 * b3
               = a1*a1*a1*a2*a2*a3*b3\<close>
    using simp_rules_for_eq by (auto simp add: mult.assoc mult.left_commute)
  have fin:\<open>a1 * b1 + a1 * a1 * a1 * a2 * b2 + a1 * a1 * a1 * a1 * a2 * a2 * a3 * b2 +
    a1 * a1 * a1 * a2 * a2 * a2 * a3 * b3 + a1 * a1 * a1 * a2 * a2 * a3 * a3 * b1 +
    a1 * a1 * a1 * a1 * a1 * a2 * a2 * a2 * a3 * a3 * b2 +a1 * a1 * a1 * a1 * a2 * a2 * a2 * a2 * 
    a3 * a3 * b3 + a1 * a1 * a2 * a2 * b3 + a1 * a1 * a2 * a3 * b1 = a1*b1 + j*a1*b1 + j^2*a1*b1 + 
    a1*a1*a1*a2*b2 + a1*a1*a1*a2*b2*j + a1*a1*a1*a2*b2*j^2 + a1*a1*a2*a2*b3 + a1*a1*a2*a2*b3*j + 
    a1*a1*a2*a2*b3*j^2\<close> 
    using simp_rules_for_eq by(auto simp:algebra_simps power2_eq_square power3_eq_cube)
  then have fin':\<open>\<dots> = (a1*b1 + a1*a1*a1*a2*b2 + a1*a1*a2*a2*b3)*(1+j+j^2)\<close>
    by(auto simp:algebra_simps power2_eq_square power3_eq_cube)
  then show graal:\<open>(a1^2+a1+1)*b1 + a1^3*(a2^2+a2+1)*b2 +a1^3*a2^3*(a3^2+a3+1)*b3 =
      -j*a1^2*a2*(a1-j)*(a2-j)*(a3-j)*(?R +j*?P +j^2*?Q)\<close>
    apply(simp only: simp_rules_for_eq(5-7)[symmetric])  
    apply(simp only:y y2 y3 distrib_left distrib_right times_divide_eq_left times_divide_eq_right)  
    apply(simp only:simp_rules_for_eq algebra_simps del:mult.assoc mult.commute) 
    apply(simp only:ko ko')
    using simp_rules_for_eq apply(auto simp add: power2_eq_square power3_eq_cube algebra_simps) (* struggle to remove this auto long algebraic formula...*) 
    apply(simp only:ko ko') apply(subst *) apply(subst **)  apply(subst ***) apply(simp)
    apply(simp only:ko ko') apply(subst fin) apply(subst fin') 
    using simp_rules_for_eq by fastforce
qed

end