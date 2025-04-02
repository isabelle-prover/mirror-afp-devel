theory Complex_Angles

imports Complex_Geometry.Elementary_Complex_Geometry

begin
section \<open>Introduction\<close>

text \<open>
Morley's trisector theorem states that in any triangle, 
the three points of intersection of the adjacent angle trisectors 
form an equilateral triangle, 
called the first Morley triangle or simply the Morley triangle. This theorem is
listed in the 100 theorem list \cite{source3}.

In this theory, we define some basics elements on complex geometry such as
axial symmetry, rotations. We also define basic property of congruent triangles in the
complex field following the model already presented in the afp \cite{Triangle-AFP}
In addition we demonstrate sines law in the complex context.

Finally we prove the Morley theorem using Alain Connes's proof \cite{source1}.
\<close>
section \<open>Angles between three complex\<close>

definition angle_c_def:\<open>angle_c a b c \<equiv> \<angle> (a-b) (c-b)\<close>

lemma angle_c_commute_pi:
  assumes \<open>angle_c a b c = pi\<close>
  shows "angle_c a b c =  angle_c c b a"
  using angle_c_def assms ang_vec_sym_pi by presburger

lemma angle_c_commute:
  assumes \<open>angle_c a b c \<noteq> pi\<close>
  shows "angle_c a b c =  -angle_c c b a"
  using angle_c_def assms ang_vec_sym by presburger

lemma angle_c_sum:
  assumes 1:\<open>a - b\<noteq>0\<close> and 2:\<open>c - b\<noteq> 0\<close> and 3:\<open>b-d \<noteq> 0\<close>
  shows\<open>\<downharpoonright>angle_c a b c + angle_c c b d\<downharpoonleft> = angle_c a b d\<close>
  using angle_c_def canon_ang_sum by force


lemma collinear_angle:\<open>collinear a b c \<Longrightarrow> a\<noteq>b \<Longrightarrow> b\<noteq>c \<Longrightarrow> c\<noteq>a \<Longrightarrow> angle_c a b c = 0 \<or> angle_c a b c = pi\<close>
  unfolding collinear_def unfolding angle_c_def  
  by (metis ang_vec_def arg_div collinear_def collinear_sym2' is_real_arg2 right_minus_eq)

lemma cdist_commute:\<open>cdist a b = cdist b a\<close>
  by (simp add: norm_minus_commute)

lemma angle_sum_triangle:
  assumes h:"a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c"
  shows   "\<downharpoonright>\<angle> (c-a) (b-a) + \<angle> (a-b) (c-b)  + \<angle> (b-c) (a-c)\<downharpoonleft> = pi"
proof -
  have f0:\<open>b-a \<noteq> 0\<close> \<open>c-a\<noteq>0\<close> \<open>b-c\<noteq>0\<close> using h by auto
  then have \<open>\<angle>c (c-a) (b-a) = abs (Arg ((b-a)/(c-a)))\<close> 
    unfolding ang_vec_def ang_vec_c_def 
    apply(subst arg_div[OF f0(1) f0(2), symmetric])
    by(simp) 
  have \<open>(b-a)/(c-a) = rcis (cmod ((b-a)/(c-a))) (Arg ((b-a)/(c-a)))\<close>
    by (simp add: rcis_cmod_Arg)
  have \<open>(b-a)/(c-a) * (c-b)/(a-b) * (a-c)/(b-c) = -1\<close>
    using h  
    by (smt (z3) divide_eq_0_iff divide_eq_minus_1_iff f0(1,2,3) minus_diff_eq mult_minus_right
        nonzero_eq_divide_eq times_divide_eq_left) 
  then have \<open>Arg ((b-a)/(c-a) * (c-b)/(a-b) * (a-c)/(b-c)) = pi\<close> 
    by (metis arg_cis cis_pi pi_canonical)
  then have \<open>Arg ((b-a)/(c-a) * (c-b)/(a-b) * (a-c)/(b-c))
 = \<downharpoonright>Arg ((b-a)/(c-a) * (c-b)/(a-b)) + Arg ((a-c)/(b-c))\<downharpoonleft>\<close>
    using arg_mult f0 
    by (metis (no_types, lifting) Arg_zero arg_mult divide_divide_eq_left' pi_neq_zero times_divide_eq_left
        times_divide_eq_right) 
  then have \<open>\<downharpoonright>Arg ((b-a)/(c-a) * (c-b)/(a-b)) + Arg ((a-c)/(b-c))\<downharpoonleft>
=\<downharpoonright>Arg ((b-a)/(c-a)) + Arg ((c-b)/(a-b)) + Arg ((a-c)/(b-c))\<downharpoonleft>\<close>
    by (metis (no_types, lifting) arg_mult canon_ang_arg canon_ang_sum divide_eq_0_iff eq_iff_diff_eq_0 h
        no_zero_divisors times_divide_eq_right)
  then show ?thesis
    using
      \<open>Arg ((b - a) / (c - a) * (c - b) / (a - b) * (a - c) / (b - c)) = \<downharpoonright>Arg ((b - a) / (c - a) * (c - b) / (a - b)) + Arg ((a - c) / (b - c))\<downharpoonleft>\<close>
      \<open>Arg ((b - a) / (c - a) * (c - b) / (a - b) * (a - c) / (b - c)) = pi\<close> arg_div h by force
qed

lemma angle_sum_triangle_c:
  assumes h:"a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c"
  shows   "\<downharpoonright>angle_c c a b + angle_c a b c  + angle_c b c a\<downharpoonleft> = pi"
  unfolding angle_c_def
  using h by (smt (z3) angle_sum_triangle h)


lemma angle_sum_triangle':
  assumes h:"a \<noteq> 0 \<and> b \<noteq> 0 \<and> c \<noteq> 0"
  shows   "\<downharpoonright>\<angle> (-a) b + \<angle> (-b) c  + \<angle> (-c) a\<downharpoonleft> = pi"
proof -
  have f0:\<open>a \<noteq> 0\<close> \<open>b\<noteq>0\<close> \<open>c\<noteq>0\<close> using h by auto
  have \<open>b/(-a) * a/(-c) * c/(-b) = -1\<close>
    using h by(auto) 
  then have f10:\<open>Arg (b/(-a) * a/(-c) * c/(-b)) = pi\<close> 
    by (metis arg_cis cis_pi pi_canonical)
  then have f1:\<open>Arg (b/(-a) * a/(-c) * c/(-b))
 = \<downharpoonright>Arg (b/(-a) * a/(-c)) + Arg (c/(-b))\<downharpoonleft>\<close>
    using arg_mult f0 
    by (metis \<open>b / - a * a / - c * c / - b = - 1\<close> divide_eq_0_iff divide_eq_minus_1_iff
        times_divide_eq_right)
  then have f2:\<open>\<downharpoonright>Arg (b/(-a) * a/(-c)) + Arg (c/(-b))\<downharpoonleft>
=\<downharpoonright>Arg (b/(-a)) + Arg (a/(-c)) + Arg (c/(-b))\<downharpoonleft>\<close>
    by (metis (no_types, lifting) arg_mult canon_ang_arg canon_ang_sum divide_eq_0_iff f0(1,2,3)
        neg_0_equal_iff_equal no_zero_divisors times_divide_eq_right)  
  then show ?thesis
    using f1 f2 arg_div h 
    by (smt (verit) f10 add.left_commute ang_vec_def neg_equal_0_iff_equal)
qed

lemma ang_c_in:\<open>angle_c a b c \<in> {-pi<..pi}\<close>
  unfolding angle_c_def by(auto simp: canon_ang) 

lemma angle_c_aac:\<open>angle_c a a c = \<downharpoonright>Arg (c-a)\<downharpoonleft>\<close>
  by (simp add: Arg_zero angle_c_def)

lemma angle_c_caa:\<open>angle_c c a a = \<downharpoonright>-Arg (c-a)\<downharpoonleft>\<close>
  by (simp add: Arg_zero angle_c_def)

lemma angle_c_neq0:\<open>angle_c p q r \<noteq> 0  \<Longrightarrow> p\<noteq>r \<close>
  unfolding angle_c_def 
  by force

end