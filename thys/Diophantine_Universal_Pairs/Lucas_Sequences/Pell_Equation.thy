theory Pell_Equation
  imports Lucas_Sequences Complex_Main "../Coding/Utils"
begin

subsection \<open>The Pell Equation\<close>

subsubsection \<open>Auxiliary facts\<close>

named_theorems real_of_int

lemma floor_of_real_of_int[real_of_int]: "\<lfloor>real_of_int x\<rfloor> = x"
  by auto

lemma floor_of_real_of_int_sub2[real_of_int]: "\<lfloor>x - real_of_int y\<rfloor> = \<lfloor>x\<rfloor> - y"
  by auto

lemma floor_of_real_of_int_mult[real_of_int]: "\<lfloor>real_of_int x * real_of_int y\<rfloor> = x * y"
  by (metis floor_of_int of_int_mult)

lemma real_of_int_inequality: "X \<le> Y \<longleftrightarrow> real_of_int X \<le> real_of_int Y" by auto
lemma real_of_int_strict_inequality: "X < Y \<longleftrightarrow> real_of_int X < real_of_int Y" by auto

lemma evenX2k:
  fixes X::int
  assumes evenX:"even X"
  shows "\<exists> k. X = 2*k"
proof -
  obtain k where "X=2*k" using evenX by auto
  then have "X=2*k" by auto
  thus ?thesis by (rule exI)
qed

lemma distrib_add_diff:
  fixes a b c d::real
  shows "(a+b)*(c-d) = a*c - a*d + b*c - b*d"
  by (simp add: algebra_simps)

lemma floor_even:
  fixes X::int
  assumes Xeven: "even X"
  shows "real_of_int \<lfloor>(real_of_int X)/2\<rfloor> = (real_of_int X)/2"
proof -
  obtain k where "X = 2*k" using Xeven by auto
  thus ?thesis by auto
qed

lemma even_to_mod2:
  fixes X Y::int
  assumes "even X = even Y"
  shows "X mod 2 = Y mod 2"
proof (cases "even X")
  case True
  have 0:"X mod 2 = 0" using \<open>even X\<close> by auto
  have "even Y" using assms \<open>even X\<close> by auto
  then have "Y mod 2 = 0" by auto
  thus "X mod 2 = Y mod 2" using 0 by auto
next
  case False
  have 1:"X mod 2 = 1" using odd_iff_mod_2_eq_one \<open>odd X\<close> by auto
  have "odd Y" using assms \<open>odd X\<close> by auto
  then have "Y mod 2 = 1" using odd_iff_mod_2_eq_one by auto
  thus "X mod 2 = Y mod 2" using 1 by auto
qed

lemma oddA_to_mod:
  fixes X Y A::int
  assumes "odd A"
  shows "A^2 mod 4 = 1"
proof -
    have "even (A-1)" using assms by auto
    then obtain k where "(A-1)=2*k" using evenX2k[of "A-1"] by auto
    then have "A = 2*k+1" by auto
    then have 1:"A^2 = 4*k^2 + 4*k +1"  using power2_sum[of "2*k" "1"] by auto
    have "(4*k^2 + 4*k) mod 4 = 0" by auto
    then have "(4*k^2 + 4*k +1) mod 4 = 1" by fastforce
    thus "A^2 mod 4 = 1" using 1 by auto
  qed

lemma sol_non_zero:
  fixes X Y A::int
  assumes sol: "X^2 - (A^2-4)*Y^2 = 4" and Alarge: "A^2>4"
  shows "X+sqrt(A^2-4)*Y \<noteq> 0"
proof(rule ccontr)
    assume 0: "\<not> X + sqrt(A^2-4)*Y \<noteq> 0"
    have A4:"(real_of_int A)^2 >4" using Alarge real_of_int_strict_inequality by auto
    have "0=(X+sqrt(A^2-4)*Y)*(X-sqrt(A^2-4)*Y)" using 0 by auto
    also have "... = (X^2 - (sqrt(A^2-4)*Y)^2)" unfolding power_def
      using square_diff_square_factored[of "X" "sqrt(A^2-4)*Y"] by (simp add: algebra_simps)
    also have "... = (X^2 - (A^2-4)*Y^2)" using A4 unfolding power_def by auto
    also have "... = 4" using sol by auto
    finally show False by auto
  qed

lemma conj_inversion:
fixes X::int and Y::int and A::int
assumes A4:"A^2 > 4" and sol:"X^2 - (A^2 - 4)*Y^2 = 4"
shows "1/2*(X-sqrt(A^2-4)*Y) = 2*inverse(X+sqrt(A^2-4)*Y)"
proof -
  define E where "E \<equiv> sqrt(A^2-4)"
  have not0: "X+sqrt(A^2-4)*Y\<noteq>0" using A4 sol sol_non_zero by auto
  have "4 \<le> A^2" using A4 by auto
  then have "4 \<le> real_of_int (A^2)"
    using real_of_int_inequality[of "4" "A^2"] by auto
  then have 0:"4 \<le> (real_of_int A)\<^sup>2" by auto
  have E2:"E^2 = A^2 - 4" unfolding E_def using 0 by auto
  have Enot0:"X+E*Y \<noteq> 0" using not0 unfolding E_def by auto
  have "(X-E*Y)*(X+E*Y) = X^2 - (E*Y)^2"
    by (simp add: power2_eq_square square_diff_square_factored)
  also have "... =X^2 - E^2*Y^2" by (simp add: algebra_simps)
  also have "... = X^2 - (A^2 - 4)*Y^2" using E2 by auto
  also have "... = 4" using sol by (simp add: algebra_simps)
  finally have "(X-E*Y)*(X+E*Y) = 4" by auto
  then have "1/2*((X-E*Y)*(X+E*Y))*(inverse (X+E*Y))
  = 2*(inverse (X+E*Y))" by (simp add: algebra_simps)
  then have "1/2*(X-E*Y)*((X+E*Y)*(inverse (X+E*Y))) = 2*(inverse (X+E*Y))"
    by (simp add: algebra_simps)
  then have "1/2*(X-E*Y) = 2*(inverse (X+E*Y))"
    using right_inverse[of "X+E*Y"] using Enot0 by auto
  thus ?thesis unfolding E_def by auto
qed

subsubsection \<open>Group structure of the solutions\<close>

(* X3,Y3 is a solution *)
lemma group_structure:
  fixes X1 X2 Y1 Y2 A::int
  assumes A4:"A^2 > 4"
  shows "(X1^2 - (A^2-4)*Y1^2 = 4) \<and> (X2^2 - (A^2-4)*Y2^2 = 4)
         \<Longrightarrow> (X1*X2 + (A^2-4)*Y1*Y2)^2 - (A^2-4)*(X1*Y2 + X2*Y1)^2 = 16"
proof -
  assume asm: "X1^2 - (A^2-4)*Y1^2 = 4 \<and>  X2^2 - (A^2-4)*Y2^2 = 4"
  define X1' where "X1' \<equiv> real_of_int X1"
  define X2' where "X2' \<equiv> real_of_int X2"
  define Y1' where "Y1' \<equiv> real_of_int Y1"
  define Y2' where "Y2' \<equiv> real_of_int Y2"
  define A' where "A' \<equiv> real_of_int A"
  define D'::real where "D'=A'^2 - 4"
  define D where "D=A^2 - 4"
  define X3'::real where "X3' \<equiv> X1'*X2' + D'*Y1'*Y2'"
  define Y3'::real where "Y3' \<equiv> X1'*Y2' + X2'*Y1'"
  define X3 where "X3 \<equiv> X1*X2 + D*Y1*Y2"
  define Y3 where "Y3 \<equiv> X1*Y2 + X2*Y1"

  have int1:"X1'^2-D'*Y1'^2=real_of_int (X1^2-D*Y1^2)"
    unfolding power_def X1'_def Y1'_def D'_def D_def A'_def by auto
  have int2:"X2'^2-D'*Y2'^2=real_of_int (X2^2-D*Y2^2)"
    unfolding power_def D'_def D_def A'_def X2'_def  Y2'_def by auto
  have int3:"X3'^2-D'*Y3'^2=real_of_int (X3^2-D*Y3^2)"
    unfolding power_def D'_def D_def A'_def X3'_def X3_def Y3'_def Y3_def X1'_def X2'_def Y1'_def Y2'_def by auto

  have "A'^2>4" unfolding A'_def using A4 real_of_int_strict_inequality by auto
  then have d:"\<bar>D'\<bar> = D'" unfolding D'_def by auto
  then have 0:"(X1' + (sqrt D') * Y1')*(X2' + (sqrt D') * Y2')= X3' +(sqrt D')*Y3'"
      unfolding X3'_def Y3'_def by (simp add: algebra_simps)
  have 1:"(X1' - (sqrt D') * Y1')*(X2' - (sqrt D') * Y2')=X3' -(sqrt D')*Y3'"
    unfolding X3'_def Y3'_def using d by (simp add: algebra_simps)

  have "X3'^2 - D'*Y3'^2 = (X3' + (sqrt D')*Y3')*(X3' - (sqrt D')*Y3')"
    unfolding power_def by (simp add: algebra_simps d)
  also have "... = (X1' + (sqrt D') * Y1')*(X2' + (sqrt D') * Y2')
        *(X1' - (sqrt D') * Y1')*(X2' - (sqrt D') * Y2')" using 0 1 by auto
  also have "... = (X1'^2 - D'*Y1'^2)* (X2'^2 - D'*Y2'^2)"
    unfolding power_def by (simp add: algebra_simps d)
  finally have "X3'^2 - D'*Y3'^2 = (X1'^2 - D'*Y1'^2)* (X2'^2 - D'*Y2'^2)"
    by auto
  then have "X3^2 - D*Y3^2 = \<lfloor>(X1'^2 - D'*Y1'^2)*(X2'^2 - D'*Y2'^2)\<rfloor>"
    using floor_of_real_of_int[of "X3\<^sup>2 - D * Y3\<^sup>2"]  int1 int2 int3 by auto
  then have "X3^2 - D*Y3^2 = (X1^2 - D*Y1^2)* (X2^2 - D*Y2^2)"
    using int1 int2 int3 floor_of_real_of_int_mult[of "X1^2 - D*Y1^2" "X2^2 - D*Y2^2"] by auto
  then have "X3^2 - D*Y3^2 = (X1^2 - D*Y1^2)* (X2^2 - D*Y2^2)"  by auto
  then have "X3^2 - D*Y3^2 = 16" using asm D_def by auto
  thus ?thesis unfolding X3_def Y3_def D_def by (simp add: algebra_simps)
qed

lemma group_structure_evenXi:
  fixes X Y A::int
  assumes  sol:"(X^2 - (A^2-4)*Y^2 = 4)" and "even A"
  shows "even X"
proof -
  obtain k where "A=2*k" using \<open>even A\<close> by auto
  then have "A^2-4 = 4*(k^2-1)" by auto
  then have 0: "((A^2-4)*Y^2 - 4) mod 4 = 0"
    using dvd_eq_mod_eq_0 by auto

  have "X^2 =((A^2-4)*Y^2 + 4)" using sol by auto
  then have "(X^2) mod 4 =((A^2-4)*Y^2 + 4) mod 4" by auto
  then have "(X^2) mod 4 = 0" using 0 by auto
  thus "even X" using dvd_eq_mod_eq_0[of "2" "(X^2)"] by auto
qed

lemma XimodYi:
  fixes X Y A::int
  assumes A4:"A^2 > 4" and sol:"(X^2 - (A^2-4)*Y^2 = 4)" and "odd A"
  shows "X mod 2 = Y mod 2"
proof -
  have 0:"A^2 mod 4 = 1" using oddA_to_mod A4 sol \<open>odd A\<close> by auto
  have "X^2 = A^2*Y^2- 4*Y^2  +4" using sol by (simp add: algebra_simps)
  then have "X^2 mod 4 = (A^2*Y^2 - 4*Y^2) mod 4" by auto
  then have 1:"X^2 mod 4 = A^2*Y^2 mod 4"
    using mod_diff_right_eq[of "A^2*Y^2" "4*Y^2" 4] by (simp add: mod_simps)

  have "A^2*Y^2 = (4*(A^2 div 4) + (A^2 mod 4))*Y^2"
    using mult_div_mod_eq[of "A^2" "4"] by auto
  then have "A^2*Y^2 = 4*(A^2 div 4)*Y^2 + (A^2 mod 4)*Y^2"
     using distrib_right [of "4*(A^2 div 4)" "(A^2 mod 4)" "Y^2"] by auto
  then have "A^2*Y^2 mod 4 =  (A^2 mod 4)*Y^2 mod 4"
    using mod_mult_self4 by (simp add: algebra_simps)
  then have "X^2 mod 4 = Y^2 mod 4" using 0 1 by auto
  then have 2:"4 dvd (X^2 - Y^2)" using mod_eq_dvd_iff by auto

  have "(X+Y)*(X-Y) = X^2 -Y^2" unfolding power_def
    using square_diff_square_factored by (simp add: algebra_simps)
  then have 3:"4 dvd (X+Y)*(X-Y)" using 2 by auto
  then have "2 dvd (X+Y)*(X-Y)"
    using dvd_trans[of 2 4 "(X+Y)*(X-Y)"] by auto
  then have "even X=even Y" by auto
  thus "X mod 2 = Y mod 2" using even_to_mod2[of "X" "Y"] by auto
qed

(* We show X3,Y3 are integers by showing that they are even. *)
lemma group_structure_int:
  fixes X1 X2 Y1 Y2 A::int
  assumes A4:"A^2 > 4" and sol1:"(X1^2 - (A^2-4)*Y1^2 = 4)"
    and sol2:"(X2^2 - (A^2-4)*Y2^2 = 4)"
  shows "even(X1*X2 + (A^2-4)*Y1*Y2) \<and> even(X1*Y2 + X2*Y1)"
proof (cases "even A")
  case True
  have evenX1X2:"even (X1*X2)" using group_structure_evenXi[of "X1" "A" "Y1"] sol1  \<open>even A\<close> by auto
  have "even ((A^2-4)*Y1*Y2)" using \<open>even A\<close> by auto
  then have con1:"even(X1*X2 + (A^2-4)*Y1*Y2)" using "evenX1X2" by auto

  have evenX1Y2:"even (X1*Y2)" using group_structure_evenXi[of "X1" "A" "Y1"] sol1 \<open>even A\<close> by auto
  have "even (X2*Y1)" using group_structure_evenXi[of "X2" "A" "Y2"] sol2 \<open>even A\<close> by auto
  then have "even(X1*Y2 + X2*Y1)" using evenX1Y2 by auto
  thus "even(X1*X2 + (A^2-4)*Y1*Y2) \<and> even(X1*Y2 + X2*Y1)" using con1 by auto
next
  case False
  have 1:"X1 mod 2 = Y1 mod 2" using XimodYi A4 sol1 \<open>odd A\<close> by auto
  have 2:"X2 mod 2 = Y2 mod 2" using XimodYi A4 sol2 \<open>odd A\<close> by auto
  have "A^2 mod 4 = 1" using oddA_to_mod A4 sol1 \<open>odd A\<close> by auto
  then have mod4:"(A^2-4) mod 4 = 1" by auto

  have 0:"(A^2-4) mod 2 = 1"
  proof -
    have "(A^2 - 4) mod 2 = (2*2*((A^2 - 4) div 4) + 1) mod 2"
      using mult_div_mod_eq[of 4 "A^2-4"] mod4
            arg_cong[of "A^2 - 4" "2*2*((A^2 - 4) div 4) + 1"]  by (simp add: mod_simps)
    also have "...  = ((2*2*((A^2 - 4) div 4) mod 2) + 1) mod 2"
      using mod_add_left_eq[of "2*2*((A^2 - 4) div 4)" 2 1] by (simp add: mod_simps)
    also have "... = 1" by auto
    finally show "(A^2 - 4) mod 2 = 1" by auto
  qed

  have "((A^2-4)*Y1*Y2) mod 2 = ((A^2-4) mod 2)*Y1*Y2 mod 2"
    using mod_mult_left_eq[of "A^2 -4" 2 "Y1*Y2"]  by (simp add: algebra_simps)
  also have "... = Y1*Y2 mod 2" using 0 by auto
  also have "... = ((Y1 mod 2)*(Y2 mod 2)) mod 2"  by (simp add: mod_simps)
  also have "... = ((X1 mod 2)*(X2 mod 2)) mod 2" using 1 2 by auto
  also have "... = X1*X2 mod 2"  by (simp add: mod_simps)
  finally have 3:"((A^2-4)*Y1*Y2) mod 2 = X1*X2 mod 2" by auto

  have "(X1*X2 -(A^2-4)*Y1*Y2) mod 2 = (X1*X2 mod 2 -((A^2-4)*Y1*Y2 mod 2)) mod 2"
    by (simp add: mod_simps)
  also have "... = (X1*X2 mod 2 - (X1*X2 mod 2)) mod 2"
    using 3 by (simp add: mod_simps)
  also have "... = 0" by auto
  finally have "(X1*X2 -(A^2-4)*Y1*Y2) mod 2 = 0" by auto
  then have con1:"even(X1*X2 + (A^2-4)*Y1*Y2)"
    using dvd_eq_mod_eq_0[of 2  "X1*X2 - (A^2-4)*Y1*Y2"] by auto

  have "(X1*Y2 + X2*Y1) mod 2 = (X1*Y2 mod 2 + (X2*Y1 mod 2)) mod 2"
    using mod_add_left_eq[of "X2*Y1" 2 "X1*Y2"]
          mod_add_right_eq[of "(X2*Y1 mod 2)" "X1*Y2" 2]  by (simp add: algebra_simps)
  also have "... = (X1*(Y2 mod 2) mod 2 + X2*(Y1 mod 2) mod 2) mod 2"
    using mod_mult_left_eq[of "Y1" 2 "X2"]
          mod_mult_left_eq[of "Y2" 2 "X1"] by (simp add: algebra_simps)
  also have "... = ((X1 mod 2)*(Y2 mod 2) mod 2 + (X2 mod 2)*(Y1 mod 2) mod 2) mod 2"
    using mod_mult_right_eq[of "Y2 mod 2" "X1" 2]
          mod_mult_right_eq[of "Y1 mod 2" "X2" 2] by (simp add: algebra_simps)
  also have "... = ((X1 mod 2)*(X2 mod 2) mod 2 + (X2 mod 2)*(X1 mod 2) mod 2) mod 2"
    using 1 2 by auto
  also have "... = 0" by (simp add: mod_simps)
  finally have "(X1*Y2 + X2*Y1) mod 2=0" by auto
  then have "even (X1*Y2 + X2*Y1)"
    using dvd_eq_mod_eq_0[of 2  "(X1*Y2 -X2*Y1)"] by auto
  thus "even(X1*X2 + (A^2-4)*Y1*Y2) \<and> even(X1*Y2 + X2*Y1)" using con1 by auto
qed

lemma group_structure_sol4:
  fixes X1 X2 Y1 Y2 A::int
  assumes Alarge:"A^2>4" and sol1:"(X1^2 - (A^2-4)*Y1^2 = 4)"
    and sol2:"(X2^2 - (A^2-4)*Y2^2 = 4)"
  defines "X3 \<equiv> X1*X2 + (A^2-4)*Y1*Y2" and "Y3 \<equiv> X1*Y2 + X2*Y1"
  shows "(floor (X3/2))^2 - (A^2-4)*(floor(Y3/2))^2 = 4"
proof -
  have evX3: "even X3" using group_structure_int Alarge sol1 sol2  unfolding X3_def by auto
  have evY3: "even Y3" using group_structure_int [of "A" "X1" "Y1" "X2" "Y2"] Alarge sol1 sol2
    unfolding Y3_def by auto
  have floorY3: "(A^2-4)*(floor (Y3/2))^2 = (A^2-4)*(Y3/2)^2"
    using evY3 floor_even[of "Y3"] by auto
  have "X3^2 - (A^2-4)*Y3^2 = 16" unfolding X3_def Y3_def
    using group_structure Alarge sol1 sol2  by auto
  then have "4 = (X3^2 - (A^2-4)*Y3^2)/4" by auto
  then have "4 = (X3/2)^2  - (A^2-4)*(Y3/2)^2" unfolding power_def by auto
  then have "4 = floor ((X3/2)^2  - real_of_int((A^2-4)*(floor(Y3/2))^2))"
    using evY3 floor_even[of "Y3"] by auto
  then show ?thesis  using floor_of_real_of_int_mult[of "floor(real_of_int X3/2)"]
    floor_of_real_of_int_sub2[of "(X3/2)^2" "(A^2-4)*(floor(Y3/2))^2"] evX3 floor_even[of "X3"]
    unfolding power_def by auto
qed

subsubsection \<open>Smallest solution\<close>
lemma smallest_sol_sublemma:
  fixes X Y A::int
  assumes Alarge: "A^2>4" and XYsol: "X^2 -(A^2-4)*Y^2 = 4"
    and "X\<ge>0" and "Y>0"
  shows "X + Y*sqrt(A^2-4) \<ge> A + sqrt(A^2 -4)"
proof -
  have sqrt_D_nonneg:"sqrt(A^2-4)\<ge>0" using Alarge
      real_of_int_strict_inequality[of "4" "A^2"] by auto
  have Y1: "Y \<ge> 1" using \<open>Y>0\<close> by auto
  then have "X^2 - (A^2-4)*Y^2 \<le> X^2 - A^2 + 4"
    using Y1 nat_le_eq_zle[of "A^2-4" "(A^2-4)*Y^2"] \<open>A^2>4\<close> by auto
  then have 2: "X \<ge> A" using XYsol \<open>X\<ge>0\<close> power2_le_imp_le by auto
  have "Y*sqrt(A^2-4) \<ge> sqrt(A^2 -4)"
    using mult_mono[of "1" "real_of_int Y" "sqrt(A^2 -4)" "sqrt(A^2 -4)"]
    sqrt_D_nonneg Y1 by auto
  thus ?thesis using 2 add_mono[of "A" "X^2" "sqrt(A^2 -4)" "sqrt(A^2-4)*Y"] by auto
qed

lemma binomial_form_sol:
  fixes X Y A::int
  assumes Alarge: "A^2>4" and XYsol: "X^2 -(A^2-4)*Y^2 = 4"
  shows "(X+Y*sqrt(A^2-4))*(X-Y*sqrt(A^2-4)) = 4"
proof -
  have real_int_A4: "real_of_int A^2 > 4"
    using Alarge real_of_int_strict_inequality[of "4" "A^2"] by auto
  then have "real_of_int Y * sqrt ((real_of_int A)\<^sup>2 - 4) *
    (real_of_int Y * sqrt ((real_of_int A)\<^sup>2 - 4)) = real_of_int Y^2 * ((real_of_int A)\<^sup>2 - 4)"
    unfolding power_def by (simp add:algebra_simps)
  then have "(X+Y*sqrt(A^2-4))*(X-Y*sqrt(A^2-4)) = X^2 - (A^2 -4)*Y^2" unfolding power_def
    using real_int_A4 square_diff_square_factored[of "X" "Y*sqrt(A^2-4)"]
    by (simp add:algebra_simps)
  thus ?thesis using XYsol by auto
qed

lemma smallest_sol:
  fixes X Y A::int
  assumes Alarge: "A^2>4" and XYsol: "X^2 -(A^2-4)*Y^2 = 4"
    and lowerbound: "2 < X + Y*sqrt(A^2-4)"
    and upperbound: "X +Y*sqrt(A^2-4) < A + sqrt(A^2-4)"
  shows "False"
proof -
  have real_int_A4: "(real_of_int A^2) > 4"
    using Alarge real_of_int_strict_inequality[of "4" "A^2"] by auto
  then have sqrt_D_pos:"sqrt(A^2-4)>0" by auto
  then have sqrt_D_nonneg:"sqrt(A^2-4)\<ge>0" by auto

  (* Cases *)
  have disj: "Y=0 \<or> (X\<ge>0 \<and> Y>0) \<or> (X\<ge>0 \<and> Y<0) \<or> (X<0 \<and> Y>0) \<or> (X<0 \<and> Y<0)"
    by auto

  (* Transforming it into a case distinction *)
  then consider
      (case0) "Y=0"
    | (case1) "X\<ge>0 \<and> Y>0"
    | (case2) "X\<ge>0 \<and> Y<0"
    | (case3) "X<0 \<and> Y>0"
    | (case4) "X<0 \<and> Y<0"
    by auto

  then show "False"
  proof (cases)
    assume Y0: "Y = 0"
    then have 0: "X^2 = 2^2" using XYsol by auto
    thus ?thesis
    proof (cases "X\<ge>0")
      assume "X \<ge> 0"
      then have "2 = X + Y*sqrt(A^2-4)" using power2_eq_imp_eq[of "X" "2"] 0 Y0 by auto
      thus ?thesis using lowerbound by auto
    next
      assume "\<not> X \<ge> 0"
      then have "X + Y*sqrt(A^2-4) = -2" using power2_eq_imp_eq[of "-X" "2"] 0 Y0 by auto
      thus "False" using lowerbound by auto
    qed
  next

    assume assm: "X\<ge>0 \<and> Y>0"
    thus "False" using smallest_sol_sublemma[of "A" "X" "Y"] Alarge XYsol upperbound by auto
  next

    assume assm: "X<0 \<and> Y<0"
    then have "(-Y)*sqrt(A^2-4) > 0"
      using mult_strict_mono'[of "0" "- real_of_int Y" "0" "sqrt(A^2-4)"] sqrt_D_pos by auto
    thus "False" using sqrt_D_nonneg assm
      add_strict_mono[of "real_of_int X" "0" "Y*sqrt(A^2-4)" "0"] lowerbound by auto
  next

    assume assm: "X<0 \<and> Y>0"
    then have "-Y*sqrt(A^2-4) < 0" using sqrt_D_pos assm
      mult_strict_mono[of "0" "- real_of_int Y" "0" "sqrt(A^2-4)"] by auto
    then have 0: "X - Y*sqrt(A^2-4) < 0" using assm
      add_le_less_mono[of "0" "X" "0" "-Y*sqrt(A^2-4)"] by auto
    then have 1: "2*(X - Y*sqrt(A^2-4)) > (X+Y*sqrt(A^2-4))*(X-Y*sqrt(A^2-4))"
      using lowerbound mult_strict_right_mono_neg[of "2" "X+Y*sqrt(A^2-4)""X-Y*sqrt(A^2-4)"] by auto
    thus "False" using binomial_form_sol[of "A" "X" "Y"] Alarge XYsol 0
      by (simp add: algebra_simps)

  next
    assume assm: "0\<le> X \<and> Y<0"
    then have 1: "X - Y*sqrt(A^2-4) \<ge> A + sqrt(A^2 -4)"
      using smallest_sol_sublemma[of "A" "X" "-Y"] XYsol Alarge assm by auto
    have "(-Y)*sqrt(A^2-4) > 0" using mult_strict_mono'[of "0" "- real_of_int Y" "0" "sqrt(A^2-4)"]
        sqrt_D_pos assm by auto
    then have "X-Y*sqrt(A^2-4) \<ge> 0" using assm
        add_le_less_mono[of "0" "X" "0" "-Y*sqrt(A^2-4)"] by auto
    then have "2*(X- Y*sqrt(A^2-4)) \<le> 4" using lowerbound mult_right_mono[of "2" "X+Y*sqrt(A^2-4)"
        "X- Y*sqrt(A^2-4)"] binomial_form_sol[of "A" "X" "Y"]  XYsol Alarge by auto
    then have 5: "X- Y*sqrt(A^2-4) \<le> 2" by auto

    thus "False"
    proof (cases "A<0")
      assume assm: "A<0"
      have "A+ sqrt(A^2-4) \<le> A+sqrt(A^2)" using real_sqrt_le_mono[of "A^2-4" "A^2"] by auto
      thus "False" using upperbound lowerbound assm by auto
    next
      assume assm: "\<not>A<0"
      then have "A>2" using power2_less_imp_less[of "2" "A"] Alarge by auto
      thus "False" using sqrt_D_pos
          add_strict_mono[of "2" "A" "0" "sqrt(A^2-4)"] 5 1 by auto
    qed
  qed
qed

subsubsection \<open>Finite generation of solutions\<close>

lemma finite_generation_nat:
  fixes X Y A::int and n::nat
  assumes sol: "X^2 - (A^2-4)*Y^2 = 4" and Alarge: "A^2 > 4"
  shows "\<exists>X3. \<exists> Y3. 2*(((X + sqrt(A^2-4)*Y)/2)^n) = X3 + sqrt(A^2-4)*Y3 \<and>
        X3^2 - (A^2-4)*Y3^2 = 4" (is "?P n")
proof (induct n)
  case 0
  have 1: "\<exists>Y1. 2*(((X + sqrt(A^2-4)*Y)/2)^0) = 2 + sqrt(A^2-4)*Y1 \<and>
        2^2 - (A^2-4)*Y1^2 = 4"
    apply (rule exI[of _ "0"])
    by auto
  show ?case
    apply (rule exI[of _ "2"])
    using 1 by auto
next
  case (Suc n)
  then have n: "?P n" using Suc.prems by simp
  then obtain X1 Y1 where X1Y1def: "2*((X + sqrt (A\<^sup>2 - 4)*Y)/2)^n=X1 + sqrt(A\<^sup>2 - 4)*Y1 \<and>
    X1\<^sup>2 - (A\<^sup>2 - 4) * Y1\<^sup>2 = 4" by blast
  define X3 where "X3 \<equiv> X*X1 + (A^2-4)*Y*Y1"
  define Y3 where "Y3 \<equiv> X*Y1 + X1*Y"
  then have X3Y3sol: "(floor (X3/2))^2 - (A^2-4)*(floor(Y3/2))^2 = 4" unfolding X3_def Y3_def
    using group_structure_sol4 X1Y1def sol Alarge by auto
  have evenX3: "even X3" unfolding X3_def using Alarge sol X1Y1def group_structure_int by auto
  have evenY3: "even Y3" unfolding Y3_def using Alarge sol X1Y1def group_structure_int by auto

  have realA4: "(real_of_int A)^2 \<ge> 4" using Alarge real_of_int_strict_inequality by auto
  have "2*(((X + sqrt(A^2-4)*Y)/2)^(n+1)) =
      2*1/2*(((X + sqrt(A^2-4)*Y)/2)^n)*(X + sqrt(A^2-4)*Y)" by auto
  also have "... = 1/2*((X1 + sqrt(A\<^sup>2-4)*Y1)*(X+sqrt(A^2-4)*Y))" using X1Y1def by auto
  also have "... = 1/2*(X1*X + sqrt(A^2-4)*Y1*X + X1*sqrt(A^2-4)*Y + (A^2-4)*Y1*Y)"
    using realA4 by (simp add: algebra_simps)
  also have "... =1/2*(X3 + Y3*sqrt(A^2-4))" unfolding X3_def Y3_def by (simp add: algebra_simps)
  also have "... =floor(X3/2) + floor(Y3/2)*sqrt(A^2-4)" using evenX3 floor_even
      evenY3 floor_even by auto
  finally have "2*(((X + sqrt(A^2-4)*Y)/2)^(n+1)) = floor(X3/2) + floor(Y3/2)*sqrt(A^2-4)"
    by auto

  then have final: "2*(((X + sqrt(A^2-4)*Y)/2)^(n+1)) = floor(X3/2) + floor(Y3/2)*sqrt(A^2-4)
      \<and> (floor (X3/2))^2 - (A^2-4)*(floor(Y3/2))^2 = 4" using X3Y3sol by auto
  have 4: "\<exists>Y2. 2*(((X + sqrt(A^2-4)*Y)/2)^(n+1)) = floor(X3/2) + Y2*sqrt(A^2-4)
      \<and> (floor (X3/2))^2 - (A^2-4)*Y2^2 = 4"
    apply (rule exI[of _ "floor(Y3/2)"])
    using final by auto
  show ?case
    apply (rule exI[of _ "floor(X3/2)"])
    using 4 by auto
qed


lemma finite_generation:
  fixes X Y A::int and n::nat
  assumes sol: "X^2 - (A^2-4)*Y^2 = 4" and "A^2>4"
  shows "\<exists>X1. \<exists> Y1. 2* (inverse ((X + sqrt(A^2-4)*Y)/2)^n) = X1 + sqrt(A^2-4)*Y1 \<and>
        X1^2 - (A^2-4)*Y1^2 = 4"
proof (cases "n=0")
  assume "n=0"
  thus ?thesis using finite_generation_nat[of "X" "A" "Y" "0"] sol \<open>A^2>4\<close> by auto
next
  assume "\<not> n=0"
  have "X + sqrt(A^2-4)*Y \<noteq> 0" using \<open>A^2>4\<close> sol sol_non_zero by auto
  then have "2*(inverse ((X+sqrt(A^2-4)*Y)/2))^n = 2*(2*inverse (X+sqrt(A^2-4)*Y))^n"
    using divide_inverse nonzero_inverse_inverse_eq[of "2"]
          nonzero_inverse_mult_distrib[of "inverse 2" "X+sqrt(A^2-4)*Y"] by auto
  then have "2*(inverse ((X+sqrt(A^2-4)*Y)/2))^n = 2*((X+sqrt(A^2-4)*(-Y))/2)^n"
    using conj_inversion \<open>A^2>4\<close> sol by auto
  thus ?thesis using finite_generation_nat[of "X" "A" "-Y" "n"] \<open>A^2>4\<close> sol by auto
qed

lemma real_arch_power:
  fixes x::real and y::real
  assumes x1: "x>1" and y1: "y \<ge> 1"
  shows "\<exists> n. x^n \<le> y \<and> y < x^(n+1)"
proof -
  define P::"nat \<Rightarrow> bool" where "P \<equiv> (\<lambda>n. y < x^n)"
  obtain m where mdef: "y < x^m" using x1 real_arch_pow by auto
  then have Pm: "P m" unfolding P_def by auto
  have "\<not> P 0" using y1 unfolding P_def by auto
  then have "\<exists>k<m. (\<forall>i\<le>k. \<not> P i) \<and> P (Suc k)"
    using Pm ex_least_nat_less[of "P" "m"] by auto
  then obtain n where "(\<forall>i\<le>n. \<not> P i) \<and> P (Suc n)" by auto
  then have "x^n \<le> y \<and> (y<x^(n+1))" unfolding P_def by auto
  thus ?thesis
      by (rule exI[of _ "n"])
qed

lemma finite_gen_all_sol:
  fixes X::int and Y::int and A::int
  defines "rho \<equiv> \<bar>A\<bar> + sqrt(A^2-4)"
          and "Z \<equiv> X + sqrt(A^2-4)*Y" and "D \<equiv> A^2-4"
  assumes Alarge: "A^2>4" and XYsol: "X^2-(A^2-4)*Y^2 = 4"
  shows "\<exists> n. Z \<in> {2*(rho/2)^n, -2*(rho/2)^n, 2*inverse(rho/2)^n, -2*inverse(rho/2)^n} \<and>
      Y \<in> {1/sqrt(D)*((rho/2)^n - inverse(rho/2)^n), -1/sqrt(D)*((rho/2)^n - inverse(rho/2)^n)}"
proof-
  define eta where "eta \<equiv> \<bar>X\<bar> + sqrt(A^2-4)*\<bar>Y\<bar>"
  have etasol: "\<bar>X\<bar>^2 - (A^2-4)*\<bar>Y\<bar>^2 =4" using XYsol by auto
  have A2: "real_of_int \<bar>A\<bar> > 2" using Alarge power2_less_imp_less[of "2" "\<bar>A\<bar>"] by auto
  have realA4: "4 < (real_of_int A)\<^sup>2" using Alarge real_of_int_strict_inequality by auto
  then have rho2: "rho > 2" unfolding rho_def
    using A2 less_trans[of "2" "\<bar>A\<bar>" "\<bar>A\<bar> + sqrt(A^2-4)"] by auto
  then have rho1: "1/2 * rho > 1" by auto

  have eta2: "eta \<ge> 2"
  proof (cases "\<bar>Y\<bar> = 0")
    assume "\<bar>Y\<bar> = 0"
    thus ?thesis unfolding eta_def using etasol power2_eq_imp_eq[of "2" "\<bar>X\<bar>"] by auto
  next
    assume "\<bar>Y\<bar> \<noteq> 0"
    then have "rho\<le>eta" unfolding eta_def rho_def
      using smallest_sol_sublemma[of "\<bar>A\<bar>" "\<bar>X\<bar>" "\<bar>Y\<bar>"] Alarge etasol by (simp add: algebra_simps)
    thus ?thesis using rho2 by auto
  qed
  then have eta1: "1/2 * eta \<ge> 1" by auto

  obtain n where ineq1: "(1/2 * rho)^n \<le> 1/2 * eta  \<and> 1/2 * eta < (1/2 * rho)^(n+1)"
    using real_arch_power[of "1/2 * rho"  "1/2 * (\<bar>X\<bar> + sqrt(A^2-4)*\<bar>Y\<bar>)"]
    eta1 rho1 unfolding eta_def by auto
  have lhspos: "2*(1/2 * rho)^n > 0" using rho1 by auto
  have 0: "inverse((1/2 * rho)^n) > 0"  using rho1 by auto
  have 1: "(1/2*rho)^n \<noteq> 0" using rho1 by auto
  then have ineq4: "2 \<le> eta* inverse(rho/2)^n" using ineq1 lhspos
      mult_mono'[of "2*(1/2 *rho)^n" "eta" "inverse((1/2 * rho)^n)" "inverse((1/2 * rho)^n)"]
      right_inverse[of "(1/2 * rho)^n"] power_inverse[of "1/2*rho" "n"] by (simp add: algebra_simps)
  have "eta* inverse((1/2 * rho)^n) < rho*(1/2*rho)^n*inverse((1/2*rho)^n)" using eta2 0
      ineq1 mult_strict_right_mono[of "eta" "2*(1/2 *rho)^(n+1)" "inverse((1/2 * rho)^n)"] by auto
  then have ineq5: "eta* inverse(rho/2)^n < rho" using right_inverse[of "(1/2*rho)^n"] 1
      power_inverse[of "rho/2" "n"] by (simp add: algebra_simps)

  have rhosol: "\<bar>A\<bar>^2 - (A^2-4) = 4" by auto
  then obtain X1 Y1 where X1Y1def: "2* (inverse (rho/2)^n) = X1 + sqrt(A^2-4)*Y1 \<and>
        X1^2 - (A^2-4)*Y1^2 = 4" unfolding rho_def
    using Alarge finite_generation[of "\<bar>A\<bar>" "A" "1" "n"] by auto
  define X3 where "X3 \<equiv> \<bar>X\<bar>*X1 + (A^2-4)*\<bar>Y\<bar>*Y1"
  define Y3 where "Y3 \<equiv> \<bar>X\<bar>*Y1 + X1*\<bar>Y\<bar>"
  have X3Y3sol: "4 = (floor(X3/2))^2 - (A^2-4)*(floor(Y3/2))^2" unfolding X3_def Y3_def
    using group_structure_sol4[of "A" "\<bar>X\<bar>" "\<bar>Y\<bar>" "X1" "Y1"] X1Y1def Alarge etasol
    unfolding X3_def Y3_def by auto
  have evX3: "even X3" using group_structure_int[of "A" "\<bar>X\<bar>" "\<bar>Y\<bar>" "X1" "Y1"]
      Alarge X1Y1def etasol unfolding X3_def by auto
  have evY3: "even Y3" using group_structure_int[of "A" "\<bar>X\<bar>" "\<bar>Y\<bar>" "X1" "Y1"]
      Alarge X1Y1def etasol unfolding Y3_def by auto

  have "eta*inverse(rho/2)^n = 1/2*eta*(2*inverse(rho/2)^n) " by auto
  also have "... = 1/2*((\<bar>X\<bar> + sqrt(A^2-4)*\<bar>Y\<bar>)*(X1+sqrt(A^2-4)*Y1))"
    unfolding eta_def using X1Y1def by auto
  also have "... = 1/2*(\<bar>X\<bar>*X1 + sqrt(A^2-4)*\<bar>Y\<bar>*X1 + \<bar>X\<bar>*sqrt(A^2-4)*Y1 + (A^2-4)*\<bar>Y\<bar>*Y1)"
    using realA4 by (simp add: algebra_simps)
  also have "... =1/2*(X3 + Y3*sqrt(A^2-4))" unfolding X3_def Y3_def by (simp add: algebra_simps)
  also have "... =floor(X3/2) + floor(Y3/2)*sqrt(A^2-4)" using evX3 floor_even evY3 floor_even
    by auto
  finally have eq: "eta*inverse(rho/2)^n = floor(X3/2) + floor(Y3/2)*sqrt(A^2-4)" by auto

  then have lowerbound: "floor(X3/2) + floor(Y3/2)*sqrt(A^2-4) \<ge> 2" using ineq4 by auto
  have upperbound: "floor(X3/2) + floor(Y3/2)*sqrt(A^2-4) < rho" using eq ineq5 by auto

  have "eta*inverse(rho/2)^n =2"
  proof(rule ccontr)
    assume "eta*inverse(rho/2)^n \<noteq> 2"
    then have strict_lowerbound: "floor(X3/2) + floor(Y3/2)*sqrt(A^2-4) > 2"
      using eq lowerbound by auto
    thus "False" using smallest_sol[of "\<bar>A\<bar>" "floor(X3/2)" "floor(Y3/2)"] Alarge upperbound X3Y3sol
      unfolding rho_def by auto
  qed
  then have "eta*(inverse((rho/2)^n)*(rho/2)^n) = 2*(rho/2)^n"
    using power_inverse[of "rho/2" "n"] by auto
  then have etan: "eta = 2*(rho/2)^n" using left_inverse[of "(rho/2)^n"] 1 by fastforce

  have "\<bar>X\<bar> - sqrt(A^2-4)*\<bar>Y\<bar> = 4*inverse(eta)" using Alarge etasol
      conj_inversion[of "A" "\<bar>X\<bar>" "\<bar>Y\<bar>"] unfolding eta_def by auto
  then have etaconj: "\<bar>X\<bar> - sqrt(A^2-4)*\<bar>Y\<bar> = 2*inverse((rho/2))^n"
    using power_inverse[of "rho/2" "n"] etan by auto

  define Zset where "Zset \<equiv> {2*(rho/2)^n, -2*(rho/2)^n, 2*inverse(rho/2)^n, -2*inverse(rho/2)^n}"
  define Yset where "Yset \<equiv> {1/sqrt(D)*((rho/2)^n - inverse(rho/2)^n),
    -1/sqrt(D)*((rho/2)^n - inverse(rho/2)^n)}"

  have Yel: "Y \<in> Yset"
  proof (cases "Y\<ge>0")
    assume "Y\<ge>0"
    then have "Y = 1/(2*sqrt(D))*(eta - (\<bar>X\<bar> - sqrt(D)*\<bar>Y\<bar>))"
      using realA4 unfolding eta_def D_def by auto
    then have "Y = 1/(2*sqrt(D))*(2*(rho/2)^n-2*inverse(rho/2)^n)"
      using etan etaconj unfolding D_def by auto
    thus ?thesis unfolding Yset_def by (simp add:algebra_simps)
  next
    assume "\<not> 0 \<le> Y"
    then have "Y = -1/(2*sqrt(D))*(eta - (\<bar>X\<bar> - sqrt(D)*\<bar>Y\<bar>))"
      using realA4 unfolding eta_def D_def by auto
    then have "Y = -1/(2*sqrt(D))*(2*(rho/2)^n-2*inverse(rho/2)^n)"
      using etan etaconj D_def by auto
    thus ?thesis unfolding Yset_def by (simp add:algebra_simps)
  qed

  (* Consider all possible combinations of signs of X and Y *)
  have disj: "(X\<ge>0 \<and> Y\<ge>0) \<or> (X<0 \<and> Y\<ge>0) \<or> (X\<ge>0 \<and> Y<0) \<or> (X<0 \<and> Y<0)" by auto

  (* Transforming it into a case distinction *)
  then consider
      (case_pos_pos) "X\<ge>0 \<and> Y\<ge>0"
      | (case_neg_pos) "X<0 \<and> Y\<ge>0"
      | (case_pos_neg) "X\<ge>0 \<and> Y<0"
      | (case_neg_pos) "X<0 \<and> Y<0"
    by auto

  then have Zel: "Z \<in> Zset"
  proof (cases)
    assume assm:"X\<ge>0 \<and> Y\<ge>0"
    thus ?thesis using etan unfolding eta_def Z_def Zset_def by auto
  next
    assume assm: "X<0 \<and> Y<0"
    then show ?thesis using etan unfolding eta_def Z_def Zset_def by auto
  next
    assume assm: "X<0 \<and> Y\<ge>0"
    then show ?thesis using etaconj unfolding Z_def Zset_def by auto
  next
    assume assm: "X\<ge>0 \<and> Y<0"
    then show ?thesis using etaconj unfolding Z_def Zset_def by auto
  qed

  have "Z \<in> {2*(rho/2)^n, -2*(rho/2)^n, 2*inverse(rho/2)^n, -2*inverse(rho/2)^n} \<and>
      Y \<in> {1/sqrt(D)*((rho/2)^n - inverse(rho/2)^n), -1/sqrt(D)*((rho/2)^n - inverse(rho/2)^n)}"
    using Zel Yel unfolding Zset_def Yset_def by auto
  then show ?thesis
      by (rule exI[of _ "n::nat"])
    qed


subsubsection \<open>Link between Pell equation and Lucas sequences\<close>

(* Lemma B.5 *)
lemma link_to_lucas:
  fixes A::int and n::nat
  assumes A4:"A^2 > 4"
  shows "inverse(sqrt(A^2-4))*((1/2*((real_of_int A)+sqrt(A^2-4)))^n -(2*inverse((real_of_int A)+sqrt(A^2-4)))^(n))= \<psi> A n"
proof (induction n rule: \<psi>_induct)
  case 0
  show ?case by auto
next
  case 1
  define A' where "A' \<equiv> real_of_int A"
  define E where "E \<equiv> sqrt(A^2-4)"
  have "A'^2 > 4" using A4 real_of_int_strict_inequality unfolding A'_def by auto
  then have "E>0" unfolding E_def A'_def by (simp add: algebra_simps)
  have sol:"A^2 - (A^2 - 4)*1 = 4" by (simp add: algebra_simps)
  have not0:"A+E \<noteq> 0" using sol_non_zero[of "A" "A" "1"]  A4 sol unfolding E_def by auto

  have "2*inverse(A+E) = 1/2*(A-E)"
    using conj_inversion[of "A" "A" 1] A4 sol not0 unfolding E_def by auto
  then have "2*inverse(A'+E) = 1/2*(A'-E)" unfolding A'_def by auto
  then have "1/2*(A'+E) - 2*inverse(A'+E) = 1/2*(A'+E)-1/2*(A'-E)" by auto
  also have "... = E" using right_diff_distrib'[of "1/2" "A'+E" "A'-E"]
    by (simp add: algebra_simps)
  finally have "1/2*(A'+E) - 2*inverse(A'+E) =E" by auto
  then have "(inverse E)*(1/2*(A'+E) - 2*inverse(A'+E)) = 1"
    using left_inverse[of "E"] \<open>E>0\<close>  by auto
  thus ?case unfolding  E_def A'_def by auto
next
  case (sucsuc n)
  define A' where "A' \<equiv> real_of_int A"
  define E where "E \<equiv> sqrt(A^2-4)"
  define Yn where "Yn\<equiv>(inverse E)*((1/2*(A'+ E ))^n -(2*inverse(A'+E))^n)"
  define Yn1 where "Yn1\<equiv>(inverse E)*((1/2*(A'+ E ))^(Suc n) -(2*inverse(A'+E))^(Suc n))"
  define Yn2 where "Yn2\<equiv>(inverse E)*((1/2*(A'+ E ))^(Suc (Suc n)) -(2*inverse(A'+E))^(Suc (Suc n)))"
  have Yn_IH:"Yn = \<psi> A n" unfolding Yn_def A'_def E_def using sucsuc.IH(2) by auto
  have Yn1_IH:"Yn1 = \<psi> A (n+1)" unfolding Yn1_def A'_def E_def using sucsuc.IH(1) by auto
  have sol:"A^2 - (A^2 - 4)*1 = 4" by (simp add: algebra_simps)
  have not0:"A+E \<noteq> 0" using sol_non_zero[of "A" "A" "1"]  A4 sol unfolding E_def by auto
  have 1:"1/2*(A'+E)*(1/2*(A'+ E))^(Suc n) = (1/2*(A'+ E))^(Suc (Suc n))"
    by auto
  have 2:"2*inverse(A'+E)*(2*inverse(A'+E))^(Suc n) = (2*inverse(A'+E))^(Suc (Suc n))"
    by auto
  have 3:"2*inverse(A'+E)*(1/2*(A'+ E))^(Suc n) = (1/2*(A'+E))^n"
    using not0 right_inverse[of "A'+E"] unfolding A'_def by auto
  have 4:"1/2*(A'+E)*(2*inverse(A'+E))^(Suc n) = (2*inverse (A'+E))^n"
    using not0 right_inverse[of "A'+E"] unfolding A'_def by auto

  have "2*inverse(A'+E) = 1/2*(A'-E)"
    using conj_inversion[of "A" "A" 1] A4 sol not0 unfolding E_def A'_def by auto
  then have "1/2*(A'+E) + 2*inverse(A'+E) = 1/2*(A'+E) + 1/2*(A'-E)" by auto
  also have "... = A'"
    using distrib_left[of "1/2" "A'+E" "A'-E"] by (simp add: algebra_simps)
  finally have "A'=1/2*(A'+E) + 2*inverse(A'+E)" by auto
  then have "A'*Yn1 = (inverse E)*(1/2*(A'+E) + 2*inverse(A'+E))
      *((1/2*(A'+ E))^(Suc n) -(2*inverse(A'+E))^(Suc n))"
    unfolding Yn1_def by auto
  also have "... = (inverse E)*(1/2*(A'+E)*(1/2*(A'+ E))^(Suc n)
                               -(1/2*(A'+E))*(2*inverse(A'+E))^(Suc n)
                               +2*inverse(A'+E)*(1/2*(A'+ E))^(Suc n)
                               -2*inverse(A'+E)*(2*inverse(A'+E))^(Suc n))"
    using distrib_add_diff by auto
  also have "... = (inverse E)*((1/2*(A'+ E))^(Suc (Suc n))
   -(2*inverse(A'+E))^n+ (1/2*(A'+ E ))^n -(2*inverse(A'+E))^(Suc (Suc n)))"
     using 1 4 2 3 by metis
  also have "... = Yn2 + Yn" unfolding Yn2_def Yn_def by (simp add:algebra_simps)
  finally have "A'*Yn1 = Yn2 + Yn" by auto
  then have "Yn2 = A'*Yn1 - Yn" by auto
  also have "... = A'*(\<psi> A (n + 1)) - (\<psi> A n)" using Yn_IH Yn1_IH by auto
  also have "... = \<psi> A (n+2)" unfolding A'_def by auto
  finally have "Yn2 = \<psi> A (n+2)" by auto
  thus ?case unfolding Yn2_def E_def A'_def by auto
qed



subsubsection \<open>Special cases\<close>

lemma lucas_pell_sublemmaA2:
  fixes Y::int
  shows "\<exists>m. Y = \<psi> 2 m \<or> Y = - \<psi> 2 m"
proof (cases "Y\<ge>0")
  assume "Y \<ge> 0"
  then have "Y = \<psi> 2 (nat Y) \<or> Y = - \<psi> 2 (nat Y)" using lucas_A_eq_2[of "(nat Y)"] by auto
  thus ?thesis by auto
next
  assume Yneg: "\<not> Y \<ge> 0"
  then have "Y = \<psi> 2 (nat(-Y)) \<or> Y = - \<psi> 2 (nat (-Y))" using lucas_A_eq_2[of "nat(-Y)"] by auto
  thus ?thesis by auto
qed

lemma lucas_pell_sublemmaAmin2:
  fixes Y::int
  shows "\<exists>m. Y = \<psi> (-2) m \<or> Y = - \<psi> (-2) m"
proof -
  obtain m where "Y = \<psi> 2 m \<or> Y = - \<psi> 2 m" using lucas_pell_sublemmaA2 by auto
  then show ?thesis
  proof
    assume Y2: "Y = \<psi> 2 m"
    thus ?thesis
    proof (cases "odd m")
      assume "odd m"
      then have "Y = \<psi> (-2) m \<or> Y = - \<psi> (-2) m" using Y2 lucas_symmetry_A2[of "-2" "m"] by auto
      thus ?thesis by auto
    next
      assume meven: "\<not> (odd m)"
      then have "Y = \<psi> (-2) m \<or> Y = - \<psi> (-2) m" using Y2 lucas_symmetry_A2[of "-2" "m"] by auto
      thus ?thesis by auto
    qed
  next
    assume Ymin2: "Y = - \<psi> 2 m"
    thus ?thesis
    proof (cases "odd m")
      assume modd: "odd m"
      then have "Y = \<psi> (-2) m \<or> Y = - \<psi> (-2) m" using lucas_symmetry_A2[of "-2" "m"] Ymin2 by auto
      thus ?thesis by auto
    next
      assume "\<not> (odd m)"
      then have meven: "even m" by auto
      then have "Y = \<psi> (-2) m \<or> Y = - \<psi> (-2) m" using lucas_symmetry_A2[of "-2" "m"] Ymin2 by auto
      thus ?thesis by auto
    qed
 qed
qed

lemma lucas_pell_sublemmaA0:
  fixes Y::int
  assumes assm: "\<exists>k. (-4)*Y^2 + 4 = k^2"
  shows "\<exists>m. Y = \<psi> 0 m \<or> Y = - \<psi> 0 m"
proof-
  obtain k where kdef: "-4*Y^2 + 4 = k^2" using assm by auto

  (* Cases *)
  have smallY: "Y \<in> {0,1,-1}"
  proof-
    have 1:"4*(1- Y^2) \<ge> 0" using kdef by auto
    then have 2: "1\<ge>Y" using power2_le_imp_le[of "Y" "1"] by auto
    have "Y \<ge> -1 " using 1 power2_le_imp_le[of "-Y" "1"] by (simp add: algebra_simps)
    thus ?thesis  using 2 by auto
  qed

  (* Transforming it into a case distinction *)
  then consider
      (case0) "Y=0"
    | (case1) "Y=1"
    | (casemin1) "Y=-1"
    by auto

  then show ?thesis
  proof (cases)
    assume "Y = 0"
    then have "Y = \<psi> 0 0 \<or> Y = - \<psi> 0 0" by auto
    then show "\<exists>m. Y = \<psi> 0 m \<or> Y = - \<psi> 0 m"
      by (rule exI[of _ 0])
  next
    assume "Y=1"
    then have "Y = \<psi> 0 1 \<or> Y = - \<psi> 0 1" by auto
    thus ?thesis
      by (rule exI[of _ 1])
  next
    assume "Y=-1"
    then have "Y=\<psi> 0 1 \<or> Y=-\<psi> 0 1" by auto
    thus ?thesis
      by (rule exI[of _ 1])
  qed
qed


lemma lucas_pell_sublemmaA1:
  fixes Y::int
  assumes assm: "\<exists>k. (1^2-4)*Y^2 + 4 = k^2"
  shows "\<exists>m. Y = \<psi> 1 m \<or> Y = - \<psi> 1 m"
proof-
  obtain k where k_def: "-3*Y^2 + 4 = k^2" using assm by auto

  (* Cases *)
  have smallY: "Y \<in> {0,1,-1}"
  proof -
    have 1:"4 -3*Y^2\<ge>0" using k_def by auto
    then have 2: "1\<ge>Y" using power2_le_imp_le[of "Y" "1"] by auto
    have "Y \<ge> -1 " using 1 power2_le_imp_le[of "-Y" "1"] by (simp add: algebra_simps)
    then show ?thesis using 2 by auto
  qed

  (* Transforming it into a case distinction *)
  then consider
      (case0) "Y=0"
    | (case1) "Y=1"
    | (casemin1) "Y=-1"
    by auto

  then show ?thesis
  proof (cases)
    assume "Y = 0"
    then have "Y = \<psi> 1 0 \<or> Y = - \<psi> 1 0" by auto
    then show "\<exists>m. (Y = \<psi> 1 m \<or> Y = - \<psi> 1 m)"
      by (rule exI[of _ 0])
  next
    assume "Y=1"
    then have "Y = \<psi> 1 1 \<or> Y = - \<psi> 1 1" by auto
    thus ?thesis
      by (rule exI[of _ 1])
  next
    assume "Y=-1"
    then have "Y=\<psi> 1 1 \<or> Y=-\<psi> 1 1" by auto
    thus ?thesis
      by (rule exI[of _ 1])
    qed
qed

lemma lucas_pell_sublemmaAmin1:
  fixes Y::int
  assumes assm: "\<exists>k. ((-1)^2-4)*Y^2 + 4 = k^2"
  shows "\<exists>m. Y = \<psi> (-1) m \<or> Y = - \<psi> (-1) m"
proof -
  obtain m where m_def: "Y = \<psi> 1 m \<or> Y = - \<psi> 1 m"
    using lucas_pell_sublemmaA1 assm by auto

  then consider
    (caseplus) "Y = \<psi> 1 m"
    | (caseminus) "Y = - \<psi> 1 m"
    by auto

  then show ?thesis
  proof (cases)
    assume "Y = \<psi> 1 m"
    then have 1: "Y = (-1)^(m+1)*(\<psi> (-1) m)" using lucas_symmetry_A2[of "1" "m"] by auto
    then show "(\<exists>m. Y = \<psi> (-1) m \<or> Y = - \<psi> (-1) m)"
    proof (cases "even m")
      assume "even m"
      then have "Y = \<psi> (-1) m \<or> Y = - \<psi> (-1) m" using 1 by auto
      thus ?thesis
        by (rule exI[of _ m])
    next
      assume "odd m"
      then have "Y = \<psi> (-1) m \<or> Y = - \<psi> (-1) m" using 1 by auto
      thus ?thesis
        by (rule exI[of _ m])
    qed
  next
    assume "Y = - \<psi> 1 m"
    then have 1: "Y = (-1)^m*(\<psi> (-1) m)" using lucas_symmetry_A2[of "1" "m"] by auto
    then show "(\<exists>m. Y = \<psi> (-1) m \<or> Y = - \<psi> (-1) m)"
    proof (cases "even m")
      assume "even m"
      then have "Y = \<psi> (-1) m \<or> Y = - \<psi> (-1) m" using 1 by auto
      thus ?thesis
        by (rule exI[of _ m])
    next
      assume "odd m"
      then have "Y = \<psi> (-1) m \<or> Y = - \<psi> (-1) m" using 1 by auto
      thus ?thesis
        by (rule exI[of _ m])
    qed
  qed
qed

subsubsection \<open>The main equivalence\<close>

lemma lucas_pell_part1:
  fixes A Y::int
  shows "(\<exists>k. (A^2-4)*Y^2 + 4 = k^2) \<Longrightarrow> (\<exists>m. Y = \<psi> A m \<or> Y = - \<psi> A m)"
proof -
  assume assumption: "\<exists>k. (A^2-4)*Y^2 + 4 = k^2"
  then obtain k where defm: "(A^2-4)*Y^2 + 4 = k^2" by auto

  have disj: "A=2 \<or> A=-2 \<or> A=0 \<or> A=1 \<or> A=-1 \<or> (A^2 > 4)"
  proof -
    have 1:"A^2 \<le> 4 \<Longrightarrow>  A \<le> 2" using power2_le_imp_le[of "A" "2"] by auto
    have "A^2 \<le> 4 \<Longrightarrow>  A \<ge>-2" using power2_le_imp_le[of "-A" "2"] by (simp add: algebra_simps)
    thus "A=2 \<or> A=-2 \<or> A=0 \<or> A=1 \<or> A=-1 \<or> (A^2 > 4)" using 1 by auto
  qed

  (* Transforming it into a case distinction *)
  then consider
      (case0) "A=0"
      | (case1) "A=1"
      | (casemin1) "A=-1"
      | (case2) "A=2"
      | (casemin2) "A=-2"
      | (caseLarge) "A^2 > 4"
    by auto

  then show ?thesis
  proof (cases)
    assume A0: "A = 0"
    show ?thesis using A0 lucas_pell_sublemmaA0 assumption by auto
  next
    assume Amin1: "A = -1"
    show ?thesis using Amin1 lucas_pell_sublemmaAmin1 assumption by auto
  next
    assume A1: "A = 1"
    show ?thesis using A1 lucas_pell_sublemmaA1 assumption by auto
  next
    assume Amin2: "A = -2"
    show ?thesis using Amin2 lucas_pell_sublemmaAmin2 assumption by auto
  next
    assume A2: "A = 2"
    show ?thesis using A2 lucas_pell_sublemmaA2 assumption by auto
  next
    assume A4:"A ^ 2 > 4"
    define D where "D\<equiv> A^2 - 4"
    define rho where "rho \<equiv> \<bar>A\<bar> + sqrt(A^2-4)"
    have realA4: "4 < (real_of_int A)\<^sup>2" using A4 real_of_int_strict_inequality by auto

    obtain n where ndef: "Y \<in> {1/sqrt(D)*((rho/2)^n - inverse(rho/2)^n),
        -1/sqrt(D)*((rho/2)^n - inverse(rho/2)^n)}"
      using finite_gen_all_sol[of "A" "k" "Y"] A4 defm unfolding rho_def D_def by auto
    have psiabsA: "1/sqrt(D)*((rho/2)^n - (inverse(rho/2))^n) = \<psi> \<bar>A\<bar> n"
        using link_to_lucas[of "\<bar>A\<bar>" "n"] A4 inverse_eq_divide[of "sqrt(\<bar>A\<bar>\<^sup>2 - 4)"]
        nonzero_inverse_mult_distrib[of "rho" "1/2"] sol_non_zero[of "\<bar>A\<bar>" "A" "1"]
        unfolding rho_def D_def by auto
    then consider (plus) "Y = 1/sqrt(D)*((rho/2)^n - inverse(rho/2)^n)" |
        (minus) "Y = -1/sqrt(D)*((rho/2)^n - inverse(rho/2)^n)" using ndef by auto
    then show ?thesis
    proof cases
      case plus
      then have YabsA: "Y = \<psi> \<bar>A\<bar> n"  using psiabsA plus by auto
      then show ?thesis
      proof (cases "A\<ge>0")
        assume Apos: "A\<ge>0"
        then have "Y = \<psi> A n \<or> Y = - \<psi> A n" using YabsA by auto
        thus ?thesis
          by (rule exI[of _ n])
      next
        assume Aneg: "\<not> A\<ge>0"
        thus ?thesis
        proof (cases "even n")
          assume evn: "even n"
          then have "Y = \<psi> A n \<or> Y = - \<psi> A n" using YabsA lucas_symmetry_A2[of "\<bar>A\<bar>" "n"] Aneg by auto
          thus ?thesis
            by (rule exI[of _ n])
        next
          assume oddn: "\<not> even n"
          then have "Y = \<psi> A n \<or> Y = - \<psi> A n" using YabsA lucas_symmetry_A2[of "\<bar>A\<bar>" "n"] Aneg by auto
          thus ?thesis
            by (rule exI[of _ n])
        qed
      qed
    next
      case minus
      then have YabsA: "Y = - \<psi> \<bar>A\<bar> n"  using psiabsA minus by auto
      then show ?thesis
      proof (cases "A\<ge>0")
        assume Apos: "A\<ge>0"
        then have "Y = \<psi> A n \<or> Y = - \<psi> A n" using YabsA by auto
        thus ?thesis
          by (rule exI[of _ n])
      next
        assume Aneg: "\<not> A\<ge>0"
        thus ?thesis
        proof (cases "even n")
          assume evn: "even n"
          then have "Y = \<psi> A n \<or> Y = - \<psi> A n" using YabsA lucas_symmetry_A2[of "\<bar>A\<bar>" "n"] Aneg by auto
          thus ?thesis
            by (rule exI[of _ n])
        next
          assume oddn: "\<not> even n"
          then have "Y = \<psi> A n \<or> Y = - \<psi> A n" using YabsA lucas_symmetry_A2[of "\<bar>A\<bar>" "n"] Aneg by auto
          thus ?thesis
            by (rule exI[of _ n])
        qed
      qed
    qed
  qed
qed

lemma lucas_pell_part3:
  fixes A::int and m::nat
  shows "(A^2-4)*(\<psi> A m)^2+4 = (\<chi> A m)^2"
proof -
  have "(A^2-4)*(\<psi> A m)^2+4 = (\<chi> A m)^2
    \<and> (A^2-4)*\<psi> A m * \<psi> A (m+1) +2*A  = \<chi> A m * \<chi> A (m+1)"
  proof (induction m rule: \<psi>_induct)
    case 0
    then show ?case by auto
  next
    case 1
    have "(A^2-4)*(\<psi> A 1)^2+4 = (\<chi> A 1)^2"
      by auto
    have "(A\<^sup>2 - 4) * \<psi> A 1 * \<psi> A (1 + 1) + 2 * A = (A^2-4) * A + 2*A"
      by auto
    also have "... = A^2*A-4*A+2*A"
      by (simp add: left_diff_distrib')
    also have "... = A*A*A-2*A"
      by (simp add: power2_eq_square)
    also have "... = A*(A*A-2)"
      by (simp add: right_diff_distrib')
    also have "... = \<chi> A 1 * \<chi> A (1+1)"
      by auto
    finally have "(A\<^sup>2 - 4) * \<psi> A 1 * \<psi> A (1 + 1) + 2 * A = \<chi> A 1 * \<chi> A (1+1)".
    then show ?case by auto
  next
    case (sucsuc m)
    note t = this
    have "(A\<^sup>2 - 4) * (\<psi> A (m + 2))\<^sup>2 + 4 = (A^2- 4) * (A * \<psi> A (m+1) - \<psi> A m)^2 + 4"
      by auto
    also have "... = (A^2- 4) * (A * \<psi> A (m+1) - \<psi> A m)*(A * \<psi> A (m+1) - \<psi> A m) + 4"
      using power2_eq_square by auto
    also have "... = (A^2- 4)*(A*\<psi> A (m+1) *(A * \<psi> A (m+1) - \<psi> A m) - \<psi> A m *(A * \<psi> A (m+1)
      - \<psi> A m))+4"
      by (simp add: left_diff_distrib')
    also have "... = (A^2-4)*(A*\<psi> A (m+1) * A * \<psi> A (m+1) - A*\<psi> A (m+1)*\<psi> A m
      - (\<psi> A m * A*\<psi> A (m+1)- \<psi> A m * \<psi> A m)) + 4"
      by (simp add: right_diff_distrib')
    also have "... = (A^2-4)*(A*\<psi> A (m+1)*A*\<psi> A (m+1)
      - 2 * A * \<psi> A (m+1) * \<psi> A m + \<psi> A m * \<psi> A m)+4"
      by auto
    also have "... =  (A^2-4)*(A^2*(\<psi> A (m+1))^2 - 2 * A * \<psi> A (m+1) * \<psi> A m + (\<psi> A m)^2)+4"
      by (simp add: power2_eq_square)
    also have "... = (A^2-4)*(A^2*(\<psi> A (m+1))^2) + (A^2-4)*(- 2 * A * \<psi> A (m+1) * \<psi> A m )
      + (A^2-4)*(\<psi> A m)^2+4"
      by (smt (verit, best) add.commute distrib_left mult_minus_left uminus_add_conv_diff)
    also have "... = A^2*((A^2-4)*(\<psi> A (m+1))^2) -2*A*(A^2-4)*\<psi> A (m+1) * \<psi> A m
      + (A^2-4)*(\<psi> A m)^2+4"
      by auto
    also have "... = A^2*((A^2-4)*(\<psi> A (m+1))^2) -2*A*(A^2-4)*\<psi> A (m+1) * \<psi> A m + (\<chi> A m)^2"
      using t by auto
    also have "... =  A^2*((A^2-4)*(\<psi> A (m+1))^2)+A^2*4-4*A^2 -2*A*(A^2-4)*\<psi> A (m+1) * \<psi> A m
      + (\<chi> A m)^2"
      by auto
    also have "... =  A^2*((A^2-4)*(\<psi> A (m+1))^2+4)-4*A^2 -2*A*(A^2-4)*\<psi> A (m+1) * \<psi> A m
      + (\<chi> A m)^2"
      using distrib_left[of "A^2" "((A^2-4)*(\<psi> A (m+1))^2)" 4] by simp
    also have "... =  A^2*(\<chi> A (m+1))^2-4*A*A -2*A*(A^2-4)*\<psi> A (m+1) * \<psi> A m + (\<chi> A m)^2"
      using t power2_eq_square by auto
    also have "... = A^2*(\<chi> A (m+1))^2 - 2*A*(2*A+(A^2-4)*\<psi> A (m+1) *\<psi> A m) + (\<chi> A m)^2"
      using distrib_left[of "2*A" "2*A" "(A^2-4)*\<psi> A (m+1) *\<psi> A m"] by auto
    also have "... = A^2*(\<chi> A (m+1))^2 - 2*A*((A^2-4)*\<psi> A m *\<psi> A (m+1) + 2*A) + (\<chi> A m)^2"
      by auto
    also have "... = A^2*(\<chi> A (m+1))^2 - 2*A*(\<chi> A m * \<chi> A (m+1)) + (\<chi> A m)^2"
      using t by auto
    also have "... = A*A*\<chi> A (m+1) * \<chi> A (m+1) - A*\<chi> A m * \<chi> A (m+1)
      - A* \<chi> A m * \<chi> A (m+1) + \<chi> A m * \<chi> A m"
      by (simp add: power2_eq_square)
    also have "... = (A*\<chi> A (m+1)) * (A*\<chi> A (m+1) - \<chi> A m) -\<chi> A m * (A*\<chi> A (m+1) - \<chi> A m)"
      by (simp add: right_diff_distrib')
    also have "... = (A*\<chi> A (m+1) - \<chi> A m) * (A*\<chi> A (m+1) - \<chi> A m)"
      by (simp add: left_diff_distrib')
    also have "... = \<chi> A (m+2) * \<chi> A (m+2)"
      by auto
    also have "... = (\<chi> A (m+2))^2"
      by (simp add: power2_eq_square)
    finally have partie_1: "(A\<^sup>2 - 4) * (\<psi> A (m + 2))\<^sup>2 + 4 = (\<chi> A (m+2))^2".

    have "(A\<^sup>2 - 4) * \<psi> A (m + 2) * \<psi> A (m + 2 + 1) + 2 * A =
      (A^2-4) * \<psi> A (m+2) * (A*\<psi> A (m+2) - \<psi> A (m+1)) + 2*A"
      by auto
    also have "... = (A^2-4)*\<psi> A (m+2) * (A*\<psi> A (m+2)) - (A^2-4)* \<psi> A (m+2)* \<psi> A (m+1) + 2*A"
      by (simp add: right_diff_distrib')
    also have "... = A*(A^2-4)*\<psi> A (m+2)*\<psi> A (m+2) - ((A^2-4)* \<psi> A (m+2)* \<psi> A (m+1) + 2*A) + 4*A"
      by auto
    also have "... = A*(A^2-4)*(\<psi> A (m+2))^2 - ((A^2-4)* \<psi> A (m+2)* \<psi> A (m+1) + 2*A) + A*4"
      by (simp add: power2_eq_square)
    also have "... = A*((A^2-4)*(\<psi> A (m+2))^2 + 4) - ((A^2-4)* \<psi> A (m+1)* \<psi> A (m+2) + 2*A)"
      by (simp add: distrib_left)
    also have "... = A*(\<chi> A (m+2))^2 - \<chi> A (m+1) * \<chi> A (m+2)"
      using t partie_1 by auto
    also have "... = \<chi> A (m+2)*A*\<chi> A (m+2) - \<chi> A (m+2) * \<chi> A (m+1)"
      using power2_eq_square by auto
    also have "... = \<chi> A (m+2)*(A*\<chi> A (m+2) - \<chi> A (m+1))"
      using right_diff_distrib[of "\<chi> A (m+2)" "A*\<chi> A (m+2)" "\<chi> A (m+1)"] by auto
    also have "... = \<chi> A (m+2) * \<chi> A (m+2+1)" by auto
    finally have "(A\<^sup>2 - 4) * \<psi> A (m + 2) * \<psi> A (m + 2 + 1) + 2 * A = \<chi> A (m+2) * \<chi> A (m+2+1)".
    then show ?case using partie_1 by simp
  qed
  then show ?thesis by auto
qed

lemma lucas_pell_part2:
  fixes A X::int
  shows "(\<exists>m. X = \<psi> A m \<or> X = - \<psi> A m) \<Longrightarrow> (\<exists>k. (A^2-4)*X^2 + 4 = k^2)"
proof -
  assume assumption: "(\<exists>m. X = \<psi> A m \<or> X = - \<psi> A m)"
  obtain m where defm: "X = \<psi> A m \<or> X = - \<psi> A m" using assumption by auto
  consider (plus) "X = \<psi> A m" | (moins) "X = -\<psi> A m" using defm by auto
  then show ?thesis
  proof cases
    case plus
    have "(A^2-4)*X^2 + 4 = (\<chi> A m)^2"
      by (simp add: lucas_pell_part3 plus)
    then show ?thesis by auto
  next
    case moins
    have "(A^2-4)*X^2 + 4 = (\<chi> A m)^2"
      by (simp add: lucas_pell_part3 moins)
    then show ?thesis by auto
  qed
qed

lemma lucas_pell_nat:
  fixes A Y :: int
  shows "(\<exists>k. (A^2-4)*Y^2 + 4 = k^2) = (\<exists>m. Y = \<psi> A m \<or> Y = - \<psi> A m)"
    and "(A^2-4)*(\<psi> A m)^2 + 4 = (\<chi> A m)^2"
  using lucas_pell_part1 lucas_pell_part3 by auto 

(* Corollary 3.3 *)
corollary lucas_pell_corollary:
  fixes A::int and X::int
  shows "is_square ((A^2-1)*X^2+1) = (\<exists>m. X = \<psi> (2*A) m \<or>  X = - \<psi> (2*A) m)"
proof -
  have carre_fois_4: "is_square n = is_square (4*n)" (is "?P1 = ?Q1") for n::int
  proof
    assume ?P1
    then obtain k where sq_k: "n = k^2" using is_square_def by auto
    have "4*n = (2*k)^2" by (simp add: algebra_simps sq_k)
    then show ?Q1 using is_square_def by blast
  next
    assume ?Q1
    then obtain k where sq_k: "4*n = k^2" using is_square_def by auto
    then have "2 dvd k"
      by (metis even_mult_iff even_numeral power2_eq_square)
    then obtain l where db: "k = 2*l" by auto
    then have "n = l^2" using sq_k by force
    then show ?P1 using is_square_def by auto
  qed
  have "(\<exists>m. X = \<psi> (2*A) m \<or>  X = - \<psi> (2*A) m) = is_square (((2*A)^2-4)*X^2 + 4)"
    using lucas_pell_part1[of "2*A" X] lucas_pell_part2[of X "2*A"] unfolding is_square_def by auto
  also have "... = is_square (4*((A^2-1)*X^2+1))"
    by (simp add: algebra_simps)
  also have "... = is_square ((A^2-1)*X^2+1)"
    using carre_fois_4 by blast
  finally have "(\<exists>m. X = \<psi> (2*A) m \<or>  X = - \<psi> (2*A) m) = is_square ((A^2-1)*X^2+1)".
  then show ?thesis by simp
qed

end
