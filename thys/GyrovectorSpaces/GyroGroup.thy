theory GyroGroup
  imports Main 
begin

class gyrogroupoid = 
  fixes gyrozero :: "'a" ("0\<^sub>g")
  fixes gyroplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 100)
begin
definition gyroaut :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "gyroaut f \<longleftrightarrow> 
       (\<forall> a b. f (a \<oplus> b) = f a \<oplus> f b) \<and> 
       bij f"
end

class gyrogroup = gyrogroupoid +
  fixes gyroinv :: "'a \<Rightarrow> 'a" ("\<ominus>")
  fixes gyr :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes gyro_left_id [simp]: "\<And> a. 0\<^sub>g \<oplus> a = a"
  assumes gyro_left_inv [simp]: "\<And> a. \<ominus>a \<oplus> a = 0\<^sub>g"
  assumes gyro_left_assoc: "\<And> a b z. a \<oplus> (b \<oplus> z) = (a \<oplus> b) \<oplus> (gyr a b z)"
  assumes gyr_left_loop: "\<And> a b. gyr a b = gyr (a \<oplus> b) b"
  assumes gyr_gyroaut: "\<And> a b. gyroaut (gyr a b)"
begin

definition gyrominus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<ominus>\<^sub>b" 100) where
  "a \<ominus>\<^sub>b b = a \<oplus> (\<ominus> b)"

end


context gyrogroup
begin

lemma gyr_distrib [simp]:
  "gyr a b (x \<oplus> y) = gyr a b x \<oplus> gyr a b y"
  by (metis gyroaut_def gyr_gyroaut)

lemma gyr_inj:
  assumes "gyr a b x = gyr a b y"
  shows "x = y"
  using assms
  by (metis UNIV_I bij_betw_iff_bijections gyr_gyroaut gyroaut_def)

text \<open>Def 2.7, (2.2)\<close>
definition cogyroplus (infixr "\<oplus>\<^sub>c" 100) where
  "a \<oplus>\<^sub>c b = a \<oplus> (gyr a (\<ominus>b) b)"

definition cogyrominus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<ominus>\<^sub>c\<^sub>b" 100) where
  "a \<ominus>\<^sub>c\<^sub>b b = a \<oplus>\<^sub>c (\<ominus> b)"

definition cogyroinv ("\<ominus>\<^sub>c") where
  "\<ominus>\<^sub>c a = 0\<^sub>g \<ominus>\<^sub>c\<^sub>b a"

text \<open>Thm 2.8, (1)\<close>
lemma gyro_left_cancel:
  assumes "a \<oplus> b = a \<oplus> c"
  shows "b = c"
  using assms
(*  by (metis gyr_inj local.gyro_left_assoc local.gyro_left_id local.gyro_left_inv) *)
proof-
  from assms
  have "(\<ominus>a) \<oplus> (a \<oplus> b) = (\<ominus>a) \<oplus> (a \<oplus> c)"
    by simp
  then have "(\<ominus>a \<oplus> a) \<oplus> gyr (\<ominus>a) a b = (\<ominus>a \<oplus> a) \<oplus> gyr (\<ominus>a) a c"
    using gyro_left_assoc
    by simp
  then have "gyr (\<ominus>a) a b = gyr (\<ominus>a) a c"
    by simp
  then show "b = c"
    using gyr_inj
    by blast
qed


text \<open>Thm 2.8, (2)\<close>

definition gyro_is_left_id where
  "gyro_is_left_id z \<longleftrightarrow> (\<forall> x. z \<oplus> x = x)"

lemma gyro_is_left_id_0 [simp]:
  shows "gyro_is_left_id 0\<^sub>g"
  by (simp add: gyro_is_left_id_def)

lemma gyr_id_1':
  assumes "gyro_is_left_id z"
  shows "gyr z a = id"
  using assms
  unfolding gyro_is_left_id_def
  by (metis eq_id_iff gyro_left_cancel gyro_left_assoc)

lemma gyr_id_1 [simp]:
  shows "gyr 0\<^sub>g a = id"
  using gyr_id_1'[of "0\<^sub>g"]
  by simp

text \<open>Thm 2.8, (3)\<close>

definition gyro_is_left_inv where
  "gyro_is_left_inv x a \<longleftrightarrow> x \<oplus> a = 0\<^sub>g"

definition gyro_is_right_inv where
  "gyro_is_right_inv x a \<longleftrightarrow> a \<oplus> x = 0\<^sub>g"

lemma gyro_is_left_inv [simp]:
  shows "gyro_is_left_inv (\<ominus>a) a"
  by (simp add: gyro_is_left_inv_def)

lemma gyr_inv_1':
  assumes "gyro_is_left_inv x a"
  shows "gyr x a = id"
  using assms gyr_left_loop[of x a]
  by (simp add: gyro_is_left_inv_def)

lemma gyr_inv_1 [simp]:
  shows "gyr (\<ominus>a) a = id"
  using gyr_left_loop[of "\<ominus>a" a]
  by simp

text \<open>Thm 2.8, (4)\<close>
lemma gyr_id [simp]:
  shows "gyr a a = id"
  by (metis gyr_id_1 gyr_left_loop gyro_left_id)

text \<open>Thm 2.8, (5)\<close>
lemma gyro_right_id [simp]:
  shows "a \<oplus> 0\<^sub>g = a"
proof-
  have "\<ominus>a \<oplus> (a \<oplus> 0\<^sub>g) = \<ominus>a \<oplus> a"
    using gyro_left_assoc
    by simp
  thus ?thesis
    using gyro_left_cancel[of "\<ominus>a"]
    by simp
qed

lemma gyro_inv_id [simp]: "\<ominus> 0\<^sub>g = 0\<^sub>g"
  by (metis gyro_left_inv gyro_right_id)

text \<open>Thm 2.8, (6)\<close>
lemma gyro_left_id_unique:
  assumes "gyro_is_left_id z"
  shows "z = 0\<^sub>g"
proof-
  have "0\<^sub>g = z \<oplus> 0\<^sub>g"
    using assms
    by (metis gyro_is_left_id_def)
  thus ?thesis
    using gyro_right_id[of z]
    by simp
qed

text \<open>Thm 2.8, (7)\<close>
lemma gyro_left_inv_right_inv:
  assumes "gyro_is_left_inv x a"
  shows "gyro_is_right_inv x a"
  using assms
  by (metis gyr_inv_1' gyro_left_cancel gyro_right_id id_apply gyro_is_left_inv_def gyro_is_right_inv_def gyro_left_assoc)

lemma gyro_rigth_inv [simp]:
  shows "a \<oplus> (\<ominus>a) = 0\<^sub>g"
  using gyro_is_right_inv_def gyro_left_inv_right_inv
  by simp

text \<open>Thm 2.8, (8)\<close>
lemma
  assumes "gyro_is_left_inv x a"
  shows "x = \<ominus>a"
  using assms
  by (metis gyr_inv_1 id_apply gyro_is_left_inv_def gyro_left_assoc gyro_left_id gyro_left_inv)

text \<open>Thm 2.8, (9)\<close>
lemma gyro_left_cancel':
  shows "\<ominus> a \<oplus> (a \<oplus> b) = b"
  by (simp add: gyro_left_assoc)

text \<open>Thm 2.8, (10)\<close>
lemma gyr_def:
  shows "gyr a b x = \<ominus> (a \<oplus> b) \<oplus> (a \<oplus> (b \<oplus> x))"
  by (metis gyro_left_cancel' gyro_left_assoc)

text \<open>Thm 2.8, (11)\<close>
lemma gyr_id_3:
  shows "gyr a b 0\<^sub>g = 0\<^sub>g"
  by (simp add: gyr_def)

text \<open>Thm 2.8, (12)\<close>
lemma gyr_inv_3:
  shows "gyr a b (\<ominus>x) = \<ominus> (gyr a b x)"
  by (metis gyroaut_def gyr_gyroaut gyr_id_3 gyro_left_cancel gyro_rigth_inv)

text \<open>Thm 2.8, (13)\<close>
lemma gyr_id_2 [simp]:
  shows "gyr a 0\<^sub>g = id"
  by (metis gyro_left_cancel eq_id_iff gyro_left_assoc gyro_left_id gyro_right_id)

lemma gyr_distrib_gyrominus: 
  shows "gyr a b (c \<ominus>\<^sub>b d) = gyr a b c \<ominus>\<^sub>b gyr a b d"
  by (metis gyroaut_def gyr_gyroaut gyr_inv_3 gyrominus_def)

lemma gyro_inv_idem [simp]: 
  shows "\<ominus> (\<ominus> a) = a"
  by (metis gyr_inv_1 gyro_left_cancel gyro_left_assoc gyro_left_id gyro_left_inv)

lemma gyr_inv_2 [simp]:
  shows "gyr a (\<ominus> a) = id"
  using gyr_inv_1[of "\<ominus>a"]
  by simp

text \<open>(2.3.a)\<close>
lemma cogyro_left_id:
  shows "0\<^sub>g \<oplus>\<^sub>c a = a"
  by (simp add: cogyroplus_def gyr_id_3)

text \<open>(2.3.b)\<close>
lemma cogyro_rigth_id:
  shows "a \<oplus>\<^sub>c 0\<^sub>g = a"
  by (simp add: cogyroplus_def gyr_id_3)

text \<open>(2.4)\<close>
lemma cogyrominus:
  shows "a \<ominus>\<^sub>c\<^sub>b b = a \<ominus>\<^sub>b gyr a b b"
  by (simp add: cogyrominus_def cogyroplus_def gyr_inv_3 gyrominus_def)

text \<open>(2.7)\<close>
lemma cogyro_right_inv:
  shows "a \<oplus>\<^sub>c (\<ominus>\<^sub>c a) = 0\<^sub>g"
  by (metis cogyroinv_def cogyrominus_def cogyroplus_def gyr_inv_2 gyro_inv_idem gyro_right_id gyro_rigth_inv iso_tuple_update_accessor_eq_assist_idI gyr_left_loop gyro_left_assoc update_accessor_accessor_eqE)

text \<open>(2.6)\<close>
lemma cogyro_left_inv:
  shows "(\<ominus>\<^sub>c a) \<oplus>\<^sub>c a = 0\<^sub>g"
  by (metis cogyroinv_def cogyro_left_id cogyrominus_def cogyro_right_inv gyro_inv_idem)

text \<open>(2.8)\<close>
lemma cogyro_gyro_inv: 
  shows "\<ominus>\<^sub>c a = \<ominus> a"
  by (simp add: cogyroinv_def cogyro_left_id cogyrominus_def)

text \<open>Thm 2.9, (2.9)\<close>
lemma gyr_nested_1:
  shows "gyr a (b \<oplus> c) \<circ> gyr b c = gyr (a \<oplus> b) (gyr a b c) \<circ> gyr a b" (is "?lhs = ?rhs")
proof
  fix x

  have "a \<oplus> (b \<oplus> (c \<oplus> x)) = (a \<oplus> b) \<oplus> gyr a b (c \<oplus> x)"
    by (simp add: gyro_left_assoc[of a b])
  also have "... = (a \<oplus> b \<oplus> (gyr a b c \<oplus> gyr a b x))"
    by simp
  also have "... = ((a \<oplus> b) \<oplus> gyr a b c) \<oplus> gyr (a \<oplus> b) (gyr a b c) (gyr a b x)"
    by (simp add: gyro_left_assoc)
  also have "... = (a \<oplus> (b \<oplus> c)) \<oplus> gyr (a \<oplus> b) (gyr a b c) (gyr a b x)"
    by (simp add: gyro_left_assoc)
  finally 
  have 1: "a \<oplus> (b \<oplus> (c \<oplus> x)) = (a \<oplus> (b \<oplus> c)) \<oplus> gyr (a \<oplus> b) (gyr a b c) (gyr a b x)"
    .


  have "a \<oplus> (b \<oplus> (c \<oplus> x)) = a \<oplus> (b \<oplus> c \<oplus> gyr b c x)"
    by (simp add: gyro_left_assoc)
  also have "... = (a \<oplus> (b \<oplus> c)) \<oplus> gyr a (b \<oplus> c) (gyr b c x)"
    by (simp add: gyro_left_assoc)
  finally have 2: "a \<oplus> (b \<oplus> (c \<oplus> x)) = (a \<oplus> (b \<oplus> c)) \<oplus> gyr a (b \<oplus> c) (gyr b c x)"
    .

  have "gyr (a \<oplus> b) (gyr a b c) (gyr a b x) = gyr a (b \<oplus> c) (gyr b c x)"
    using 1 2
    by (metis gyro_left_cancel')

  thus "?lhs x = ?rhs x"
    by simp
qed

text \<open>Thm 2.9, (2.15)\<close>
lemma gyr_nested_1': 
  shows "gyr (a \<oplus> b) (\<ominus> (gyr a b b)) \<circ> gyr a b = id"
  by (metis comp_id gyr_inv_2 gyr_inv_3 gyr_nested_1 gyr_id_2 gyro_rigth_inv)

text \<open>Thm 2.9, (2.10)\<close>
lemma gyr_nested_2: 
  shows "gyr a (\<ominus> (gyr a b b)) \<circ> gyr a b = id"
proof-
  have "gyr (a \<oplus> b) (gyr a b (\<ominus> b)) = gyr a (\<ominus> (gyr a b b))" 
    by (metis gyr_inv_3 gyro_left_assoc gyr_left_loop gyro_right_id gyro_rigth_inv)
  thus ?thesis
    using gyr_nested_1[of a b "\<ominus> b"]
    by simp
qed

text \<open>Thm 2.9, (2.11)\<close>
lemma gyr_auto_id1: 
  shows "gyr (\<ominus> a) (a \<oplus> b) \<circ> gyr a b = id"
  using gyr_nested_1[of "\<ominus> a" a b]
  by simp

text \<open>Thm 2.9, (2.12)\<close>
lemma gyr_auto_id2:
  shows "gyr b (a \<oplus> b) \<circ> gyr a b = id"
  by (metis gyr_auto_id1 gyro_left_cancel' gyr_left_loop)

text \<open>Thm 2.10, (2.18)\<close>
lemma gyro_plus_def_co:
  shows "a \<oplus> b = a \<oplus>\<^sub>c gyr a b b"
  by (simp add: cogyroplus_def gyr_nested_2 pointfree_idE)

text \<open>Thm 2.11, (2.21)\<close>
lemma gyro_polygonal_addition_lemma:
  shows "(\<ominus> a \<oplus> b) \<oplus> gyr (\<ominus>a) b (\<ominus> b \<oplus> c) = \<ominus> a \<oplus> c"
proof-
  have "gyr (\<ominus>a) b (\<ominus> b \<oplus> c) = gyr (\<ominus>a) b (\<ominus> b) \<oplus> gyr (\<ominus> a) b c"
    by simp
  hence "(\<ominus> a \<oplus> b) \<oplus> gyr (\<ominus>a) b (\<ominus> b \<oplus> c) = 
        (\<ominus> a \<oplus> b) \<oplus> (gyr (\<ominus>a) b (\<ominus> b) \<oplus> gyr (\<ominus> a) b c)"
    by simp
  also have "... = ((\<ominus> a \<oplus> b) \<ominus>\<^sub>b gyr (\<ominus> a) b b) \<oplus> (gyr ((\<ominus> a) \<oplus> b) (\<ominus> (gyr (\<ominus> a) b b)) \<circ> gyr (\<ominus> a) b) c"
    by (metis calculation gyr_inv_3 gyr_nested_1' gyro_left_cancel' gyrominus_def gyro_right_id id_apply gyro_left_assoc)
  also have "... = (\<ominus> a \<oplus> (b \<ominus>\<^sub>b b)) \<oplus> c"
    by (metis gyr_inv_3 gyr_nested_1' gyrominus_def id_apply gyro_left_assoc)
  also have "... = \<ominus> a \<oplus> c"
    by (simp add: gyrominus_def)
  finally
  show ?thesis
    .
qed

text \<open>Thm 2.12, (2.23)\<close>
lemma gyro_translation_1:
  shows "\<ominus> (\<ominus>a \<oplus> b) \<oplus> (\<ominus>a \<oplus> c) = gyr (\<ominus> a) b (\<ominus>b \<oplus> c)"
  by (metis gyr_def gyro_left_cancel')

text \<open>Thm 3.13, (3.33a)\<close>
lemma gyro_translation_2a:
  shows "\<ominus> (a \<oplus> b) \<oplus> (a \<oplus> c) = gyr a b (\<ominus>b \<oplus> c)"
  by (metis gyr_def gyro_left_cancel')

definition gyro_polygonal_add ("\<oplus>\<^sub>p") where
  "\<oplus>\<^sub>p a b c = (\<ominus> a \<oplus> b) \<oplus> gyr (\<ominus> a) b (\<ominus> b \<oplus> c)"

(* ----------------------- *)

text \<open>Thm 2.15, (2.34, 2.35)\<close>
lemma gyro_equation_right:
  shows "a \<oplus> x = b \<longleftrightarrow> x = \<ominus>a \<oplus> b"
  by (metis gyro_left_cancel')

text \<open>Thm 2.15, (2.36, 2.37)\<close>
lemma gyro_equation_left:
  shows "x \<oplus> a = b \<longleftrightarrow> x = b \<ominus>\<^sub>c\<^sub>b a"
  by (metis cogyrominus gyr_def gyr_inv_3 gyro_equation_right gyrominus_def gyro_right_id gyr_left_loop)

lemma oplus_ominus_cancel [simp]:
  shows "y = x \<oplus> (\<ominus> x \<oplus> y)"
  by (metis local.gyro_equation_right)

text \<open>(2.39)\<close>
lemma cogyro_right_cancel':
  shows "(b \<ominus>\<^sub>c\<^sub>b a) \<oplus> a = b"
  by (simp add: gyro_equation_left)

text \<open>(2.40)\<close>
lemma gyro_right_cancel'_dual:
  shows "(b \<ominus>\<^sub>b a) \<oplus>\<^sub>c a = b"
  by (metis cogyrominus_def gyro_equation_left gyro_inv_idem gyrominus_def)

(* ----------------------- *)

text \<open>Thm 2.19 (2.48)\<close>
lemma gyroaut_gyr_commute_lemma:
  assumes "gyroaut A"
  shows "A \<circ> gyr a b = gyr (A a) (A b) \<circ> A" (is "?lhs = ?rhs")
proof
  fix x
  have "(A a \<oplus> A b) \<oplus> (A \<circ> gyr a b) x = A((a \<oplus> b) \<oplus> gyr a b x)"
    using assms gyroaut_def
    by auto
  also have "... = A (a \<oplus> (b \<oplus> x))"
    by (simp add: gyro_left_assoc)
  also have "... = A a \<oplus> (A b \<oplus> A x)"
    using assms gyroaut_def
    by auto
  also have "... = (A a \<oplus> A b) \<oplus> (gyr (A a) (A b) (A x))"
    by (simp add: gyro_left_assoc)
  finally
  show "?lhs x = ?rhs x"
    using gyro_left_cancel
    by auto
qed

text \<open>Thm 2.20\<close>
lemma gyroaut_gyr_commute: 
  assumes "gyroaut A"
  shows "gyr a b = gyr (A a) (A b) \<longleftrightarrow> A \<circ> gyr a b = gyr a b \<circ> A"
proof
  assume "gyr a b = gyr (A a) (A b)"
  thus "A \<circ> gyr a b = gyr a b \<circ> A"
    using gyroaut_gyr_commute_lemma[OF assms]
    by metis
next
  assume *: "A \<circ> gyr a b = gyr a b \<circ> A"
  have "gyr (A a) (A b) = A \<circ> gyr a b \<circ> (inv A)"
    using gyroaut_gyr_commute_lemma[OF assms, of a b]
    by (metis gyroaut_def assms bij_is_surj comp_id o_assoc surj_iff)
  also have "... = gyr a b"
    using *
    by (metis gyroaut_def assms bij_is_surj comp_assoc comp_id surj_iff)
  finally 
  show "gyr a b = gyr (A a) (A b)"
    by simp
qed

text \<open>2.50\<close>
lemma gyr_commute_misc_1:
  shows "gyr (gyr a b a) (gyr a b b) = gyr a b"
  by (metis gyroaut_gyr_commute gyr_gyroaut)

text \<open>Thm 2.21 (2.52)\<close>
definition
  "cogyroaut f \<longleftrightarrow> ((\<forall>a b. f (a \<oplus>\<^sub>c b) = f a \<oplus>\<^sub>c f b) \<and> bij f)"

lemma gyro_coaut_iff_gyro_aut:
  shows "gyroaut f \<longleftrightarrow> cogyroaut f"
proof
  assume "gyroaut f"
  thus "cogyroaut f"
    unfolding gyroaut_def cogyroaut_def
    by (smt cogyroplus_def gyr_def gyro_left_cancel gyro_right_id gyro_rigth_inv)
next
  assume "cogyroaut f"
  thus "gyroaut f"
    unfolding gyroaut_def cogyroaut_def
    by (metis bij_pointE cogyro_left_id cogyrominus_def cogyro_rigth_id gyro_equation_left gyro_right_cancel'_dual gyro_left_id gyrominus_def)
qed


(* ----------------------- *)

text \<open>Thm 2.25, (2.76)\<close>
lemma gyroplus_inv:
  shows "\<ominus> (a \<oplus> b) = gyr a b (\<ominus> b \<ominus>\<^sub>b a)"
  by (metis gyr_def gyro_equation_right gyrominus_def gyro_rigth_inv)

text \<open>Thm 2.25, (2.77)\<close>
lemma inv_gyr:
  shows "inv (gyr a b) = gyr (\<ominus>b) (\<ominus>a)"
  by (metis fun.map_id0 gyr_auto_id2 gyr_inv_2 gyr_nested_1 gyro_left_cancel' gyrominus_def gyroplus_inv id_apply inv_unique_comp gyr_left_loop)

text \<open>Thm 2.26, (2.86)\<close>
lemma gyr_aut_inv_1:
  shows "inv (gyr a b) = gyr a (\<ominus> (gyr a b b))"
  by (metis comp_eq_dest_lhs eq_id_iff gyr_nested_2 inv_unique_comp)

text \<open>Thm 2.26, (2.87)\<close>
lemma gyr_aut_inv_2:
  shows "inv (gyr a b) = gyr (\<ominus> a) (a \<oplus> b)"
  by (metis gyr_auto_id2 gyro_left_cancel' inv_unique_comp gyr_left_loop)

text \<open>Thm 2.26, (2.88)\<close>
lemma gyr_aut_inv_3:
  shows "inv (gyr a b) = gyr b (a \<oplus> b)"
  by (metis gyr_auto_id2 gyro_left_cancel' inv_unique_comp gyr_left_loop)

text \<open>Thm 2.26, (2.89)\<close>
lemma gyr_1:
  shows "gyr a b = gyr b (\<ominus>b \<ominus>\<^sub>b a)"
  by (metis inv_gyr gyr_aut_inv_2 gyro_inv_idem gyrominus_def)

text \<open>Thm 2.26, (2.90)\<close>
lemma gyr_2:
  shows "gyr a b = gyr (\<ominus>a) (\<ominus>b \<ominus>\<^sub>b a)"
  using inv_gyr gyr_aut_inv_3 gyrominus_def by auto

text \<open>Thm 2.26, (2.91)\<close>
lemma gyr_3:
  shows "gyr a b = gyr (\<ominus> (a \<oplus> b)) a"
  by (metis gyr_1 gyro_inv_idem gyro_left_cancel' gyrominus_def)

text \<open>Thm 2.27, (2.92)\<close>
lemma gyr_even:
  shows "gyr (\<ominus> a) (\<ominus> b) = gyr a b"
  by (metis cogyro_right_cancel' gyr_aut_inv_3 inv_gyr local.gyr_left_loop)

text \<open>Thm 2.27, (2.93)\<close>
lemma inv_gyr_sym:
  shows "inv (gyr a b) = gyr b a"
  by (simp add: inv_gyr gyr_even)

text \<open>Thm 2.27, (2.94a)\<close>
lemma gyr_nested_3:
  shows "gyr b (\<ominus> (gyr b a a)) = gyr a b"
  using gyr_aut_inv_1 inv_gyr_sym
  by auto

text \<open>Thm 2.27, (2.94b)\<close>
lemma gyr_nested_4:
  shows "gyr b (gyr b (\<ominus> a) a) = gyr a (\<ominus> b)"
  by (metis gyr_aut_inv_1 inv_gyr_sym gyr_even gyro_inv_idem)

text \<open>Thm 2.27, (2.94c)\<close>
lemma gyr_nested_5:
  shows "gyr (\<ominus> (gyr a b b)) a = gyr a b"
  by (metis inv_gyr_sym gyr_nested_3)

text \<open>Thm 2.27, (2.94d)\<close>
lemma gyr_nested_6:
  shows "gyr (gyr a (\<ominus> b) b) a = gyr a (\<ominus> b)"
  by (metis inv_gyr inv_gyr_sym gyr_nested_4 gyro_inv_idem)

text \<open>Thm 2.28, (i)\<close>
lemma gyro_right_assoc:
  shows "(a \<oplus> b) \<oplus> c = a \<oplus> (b \<oplus> gyr b a c)"
  by (metis gyr_aut_inv_2 inv_gyr_sym gyro_equation_right gyro_left_assoc)

text \<open>Thm 2.28, (ii)\<close>
lemma gyr_right_loop:
  shows "gyr a b = gyr a (b \<oplus> a)"
  using gyr_aut_inv_3 inv_gyr_sym by auto

text \<open>Thm 2.29, (a)\<close>
lemma gyr_left_coloop:
  shows "gyr a b = gyr (a \<ominus>\<^sub>c\<^sub>b b) b"
  by (metis cogyro_right_cancel' gyr_left_loop)

text \<open>Thm 2.29, (b)\<close>
lemma gyr_rigth_coloop:
  shows "gyr a b = gyr a (b \<ominus>\<^sub>c\<^sub>b a)"
  by (metis inv_gyr_sym gyr_left_coloop)

text \<open>Thm 2.30, (2.101a)\<close>
lemma gyr_misc_1:
  shows "gyr (a \<oplus> b) (\<ominus> a) = gyr a b"
  by (metis gyr_aut_inv_2 inv_gyr_sym)

text \<open>Thm 2.30, (2.101b)\<close>
lemma gyr_misc_2:
  shows "gyr (\<ominus> a) (a \<oplus> b) = gyr b a"
  using gyr_aut_inv_2 inv_gyr_sym by auto

text \<open>Thm 2.31, (2.103)\<close>
lemma coautomorphic_inverse:
  shows "\<ominus> (a \<oplus>\<^sub>c b) = (\<ominus> b) \<oplus>\<^sub>c (\<ominus> a)"
proof-
  have "a \<oplus>\<^sub>c b = a \<oplus> gyr a (\<ominus> b) b"
    by (simp add: cogyroplus_def)
  also have "... = \<ominus> (gyr a (gyr a (\<ominus> b) b) (\<ominus> (gyr a (\<ominus> b) b) \<ominus>\<^sub>b a))"
    by (metis gyro_inv_idem gyroplus_inv)
  also have "... = gyr a (\<ominus> (gyr a (\<ominus> b) (\<ominus>b))) (\<ominus> (\<ominus> (gyr a (\<ominus> b) b) \<ominus>\<^sub>b a))"
    by (simp add: gyr_inv_3)
  also have "... = (inv (gyr a (\<ominus> b))) (\<ominus> (\<ominus> (gyr a (\<ominus> b) b) \<ominus>\<^sub>b a))"
    by (simp add: gyr_aut_inv_1)
  also have "... = \<ominus> (\<ominus> b \<ominus>\<^sub>b (inv (gyr a (\<ominus> b))) a)"
    by (metis cogyrominus cogyroplus_def inv_gyr_sym gyr_even gyr_inv_3 gyr_nested_3 gyro_equation_left gyro_inv_idem gyro_left_cancel' gyrominus_def cogyro_right_cancel' gyroplus_inv)
  also have "... = \<ominus> ((\<ominus> b) \<oplus>\<^sub>c (\<ominus> a))"
    by (simp add: cogyroplus_def inv_gyr_sym gyr_inv_3 gyrominus_def)
  finally 
  have "a \<oplus>\<^sub>c b = \<ominus> ((\<ominus> b) \<oplus>\<^sub>c (\<ominus> a))"
    .
  thus ?thesis
    by simp
qed


text \<open>Thm 2.32, (2.105a)\<close>
lemma gyr_misc_3:
  shows "gyr a b b = \<ominus> (\<ominus> (a \<oplus> b) \<oplus> a)"
  by (metis gyr_3 gyro_inv_idem gyro_left_cancel' gyrominus_def gyroplus_inv)

text \<open>Thm 2.32, (2.105b)\<close>
lemma gyr_misc_4: 
  shows "gyr a (\<ominus> b) b = \<ominus> (a \<ominus>\<^sub>b b) \<oplus> a"
  by (simp add: gyr_def gyrominus_def)


text \<open>Thm 2.35, (2.124)\<close>
lemma mixed_gyroassoc_law: "(a \<oplus>\<^sub>c b) \<oplus> c = a \<oplus> gyr a (\<ominus> b) (b \<oplus> c)"
  by (metis (full_types) cogyroplus_def gyr_nested_6 gyro_right_assoc gyr_distrib)

(* ------------------------------------------------- *)

text \<open>Thm 3.2\<close>
lemma gyrocommute_iff_gyroatomorphic_inverse:
  shows "(\<forall> a b. \<ominus> (a \<oplus> b) = \<ominus> a \<ominus>\<^sub>b b) \<longleftrightarrow> (\<forall> a b. a\<oplus>b = gyr a b (b \<oplus> a))"
  by (metis gyr_even gyro_inv_idem gyrominus_def gyroplus_inv)

text \<open>Thm 3.4\<close>
lemma cogyro_commute_iff_gyrocommute: 
   "(\<forall> a b. a \<oplus>\<^sub>c b = b \<oplus>\<^sub>c a) \<longleftrightarrow> (\<forall> a b. a\<oplus>b = gyr a b (b \<oplus> a))" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  have "\<forall> a b. a \<oplus>\<^sub>c b = b \<oplus>\<^sub>c a \<longleftrightarrow> \<ominus> (\<ominus>b \<ominus>\<^sub>b gyr b (\<ominus> a) a) = b \<oplus> gyr b (\<ominus> a) a"
    by (metis coautomorphic_inverse cogyroplus_def gyr_even gyr_inv_3 gyro_inv_idem gyrominus_def)
  thus ?thesis
    by (smt (verit, ccfv_threshold) cogyroplus_def gyr_even gyro_equation_right gyro_inv_idem gyrominus_def gyro_right_cancel'_dual gyroplus_inv)
qed

end

class gyrocommutative_gyrogroup = gyrogroup + 
  assumes gyro_commute: "a \<oplus> b = gyr a b (b \<oplus> a)"
begin
lemma gyroautomorphic_inverse:
  shows "\<ominus> (a \<oplus> b) = \<ominus> a \<ominus>\<^sub>b b"
  using gyro_commute gyrocommute_iff_gyroatomorphic_inverse 
  by blast

lemma cogyro_commute:
  shows "a \<oplus>\<^sub>c b = b \<oplus>\<^sub>c a"
  using cogyro_commute_iff_gyrocommute gyro_commute
  by blast

text \<open>Thm 3.5 (3.15)\<close>
lemma gyr_commute_misc_2:
  shows "gyr a b \<circ> gyr (b \<oplus> a) c = gyr a (b \<oplus> c) \<circ> gyr b c"
  by (metis gyr_gyroaut gyroaut_gyr_commute_lemma gyr_nested_1 gyro_commute)

text \<open>Thm 3.6 (3.17, 3.18)\<close>
lemma gyr_parallelogram:
  assumes "d = (b \<oplus>\<^sub>c c) \<ominus>\<^sub>b a"
  shows "gyr a (\<ominus> b) \<circ> gyr b (\<ominus> c) \<circ> gyr c (\<ominus> d) = gyr a (\<ominus> d)"
proof-
  have *: "\<forall> a' b' c'. gyr a' (b' \<oplus> a') \<circ> gyr (b' \<oplus> a') c' = gyr a' (b' \<oplus> c') \<circ> gyr (b' \<oplus> c') c'"
    using gyr_commute_misc_2 gyr_left_loop gyr_right_loop
    by auto
  let ?a' = "\<ominus> c"
  let ?c' = "\<ominus> a"
  let ?b' = "b \<ominus>\<^sub>c\<^sub>b ?a'"

  have "?b' \<oplus> ?c' = d"
    by (simp add: assms cogyrominus_def gyrominus_def)
  moreover
  have "b \<ominus>\<^sub>c\<^sub>b \<ominus> c \<oplus> \<ominus> c = b"
    by (simp add: cogyro_right_cancel')
  ultimately
  have "gyr (\<ominus> c) b \<circ> gyr b (\<ominus> a) = gyr (\<ominus> c) d \<circ> gyr d (\<ominus> a)"
    using  *[rule_format, of "?a'" "?b'" "?c'"]
    by simp
  then show ?thesis
    by (smt bij_is_inj gyroaut_def gyr_gyroaut inv_gyr_sym gyr_even gyro_inv_idem o_inv_distrib o_inv_o_cancel)
qed


text \<open>Thm 3.8 (3.23, 3.24)\<close>
lemma gyr_parallelogram_iff:
  "d = (b  \<oplus>\<^sub>c c) \<ominus>\<^sub>b a \<longleftrightarrow> \<ominus>c \<oplus> d = gyr c (\<ominus>b) (b \<ominus>\<^sub>b a)"
proof-
  have  "(b  \<oplus>\<^sub>c c) \<ominus>\<^sub>b a = (c  \<oplus>\<^sub>c b)  \<ominus>\<^sub>b (gyr  b (\<ominus>c)  (gyr c (\<ominus>b) a))"
    by (metis cogyro_commute local.gyr_def local.gyr_even local.gyro_right_assoc local.oplus_ominus_cancel)
    
  moreover have " (c  \<oplus>\<^sub>c b)  \<ominus>\<^sub>b (gyr  b (\<ominus>c)  (gyr c (\<ominus>b) a)) = 
   (c  \<oplus>\<^sub>c b)  \<ominus>\<^sub>b (gyr  c (gyr c (\<ominus>b) b)  (gyr c (\<ominus>b) a))"
    using local.gyr_nested_4 by auto

  moreover have "  (c  \<oplus>\<^sub>c b)  \<ominus>\<^sub>b (gyr  c (gyr c (\<ominus>b) b)  (gyr c (\<ominus>b) a)) =
    c  \<oplus> (gyr  c (\<ominus>b) b)  \<ominus>\<^sub>b (gyr  c (gyr c (\<ominus>b) b)  (gyr c (\<ominus>b) a))"
    using local.cogyroplus_def by presburger

  moreover have "  c  \<oplus> (gyr  c (\<ominus>b) b)  \<ominus>\<^sub>b (gyr  c (gyr c (\<ominus>b) b)  (gyr c (\<ominus>b) a)) =
    c  \<oplus> ((gyr  c (\<ominus>b) b) \<ominus>\<^sub>b  (gyr  c (\<ominus>b) a)) "
    by (simp add: local.gyr_inv_3 local.gyro_left_assoc local.gyrominus_def)
  moreover have "(b  \<oplus>\<^sub>c c) \<ominus>\<^sub>b a =  c \<oplus> gyr c (\<ominus>b) (b \<ominus>\<^sub>b a)"
    by (simp add: calculation(1) calculation(2) calculation(3) calculation(4) local.gyr_distrib_gyrominus)
  ultimately show ?thesis
    by (metis local.oplus_ominus_cancel)
qed

text \<open>Thm 3.9 (3.26)\<close>
lemma gyr_commute_misc_3:
  "gyr a b (b \<oplus> (a \<oplus> c)) = (a \<oplus> b) \<oplus> c"
  using gyr_distrib gyro_commute gyro_left_assoc gyro_right_assoc
  by (metis (no_types, lifting))

text \<open>Thm 3.10 (3.28)\<close>
lemma gyro_left_right_cancel:
  shows "(a \<oplus> b) \<ominus>\<^sub>b a = gyr a b b"
  by (metis gyroautomorphic_inverse gyr_misc_3 gyro_inv_idem)

text \<open>Thm 3.11 (3.29)\<close>
lemma cogyro_plus_def:
  shows "a \<oplus>\<^sub>c b = a \<oplus> ((\<ominus> a \<oplus> b) \<oplus> a)"
  by (metis cogyro_commute_iff_gyrocommute cogyroplus_def gyro_commute gyro_equation_right gyro_right_assoc)

text \<open>Thm 3.12 (3.31)\<close>
lemma cogyro_commute_misc1:
  shows "a \<oplus>\<^sub>c (a \<oplus> b) = a \<oplus> (b \<oplus> a)"
  by (simp add: cogyro_plus_def gyro_left_cancel')

text \<open>Thm 3.13 (3.33b)\<close>
lemma gyro_translation_2b:
  shows "(a \<oplus> b) \<ominus>\<^sub>b (a \<oplus> c) = gyr a b (b \<ominus>\<^sub>b c)"
  by (metis gyr_commute_misc_3 gyroautomorphic_inverse gyro_equation_right gyrominus_def)

text \<open>Thm 3.14 (3.34)\<close>

text \<open>(3.37)\<close>
lemma gyr_commute_misc_4':
  shows "gyr a (b \<oplus> c) = gyr a b \<circ> gyr (b \<oplus> a) c \<circ> gyr c b"
proof-
  have "gyr a b \<circ> gyr (b \<oplus> a) c = gyr (a \<oplus> b) (gyr a b c) \<circ> gyr a b"
    by (simp add: gyr_commute_misc_2 local.gyr_nested_1)
  hence "gyr a (b \<oplus> c) \<circ> gyr b c = gyr a b \<circ> gyr (b \<oplus> a) c"
    by (simp add: gyr_commute_misc_2)
  thus ?thesis
    by (metis comp_assoc comp_id local.gyr_auto_id2 local.gyr_right_loop)
qed

text \<open>(3.38)\<close>
lemma gyr_commute_misc_4'':
  shows "gyr (\<ominus>b \<oplus> d) (b \<oplus> c) = gyr (\<ominus> b) d \<circ> gyr d c \<circ> gyr c b"
  by (metis gyr_commute_misc_4' local.gyr_misc_1 local.gyro_inv_idem local.gyro_left_cancel')

text \<open>Thm 3.14 (3.34)\<close>
lemma gyro_commute_misc_4:
  shows "gyr (\<ominus> a \<oplus> b) (a \<ominus>\<^sub>b c) = gyr a (\<ominus> b) \<circ> gyr b (\<ominus> c) \<circ> gyr c (\<ominus> a)"
  by (metis gyr_commute_misc_4' gyr_even gyr_misc_1 gyro_inv_idem gyro_left_cancel' gyrominus_def)

text \<open>Thm 3.15 (3.40)\<close>
lemma gyr_inv_2':
  shows "gyr a (\<ominus>b) = gyr (\<ominus> a \<oplus> b) (a \<oplus> b) \<circ> gyr a b"
  by (metis comp_id gyr_commute_misc_2 local.gyr_even local.gyr_id local.gyr_misc_1 local.gyro_inv_idem local.gyro_left_cancel')

text \<open>Thm 3.17 (3.48)\<close>
lemma gyr_master':
  shows "gyr a x \<circ> gyr (\<ominus> (x \<oplus> a)) (x \<oplus> b) \<circ> gyr x b = gyr (\<ominus> a) b"
  by (metis gyr_commute_misc_4' gyroautomorphic_inverse gyr_even gyr_misc_1 gyro_left_cancel' gyrominus_def)

text \<open>(3.51)\<close>
lemma gyr_master:
  shows "gyr a x \<circ> gyr (x \<oplus> a) (\<ominus> (x \<oplus> b)) \<circ> gyr x b = gyr (\<ominus> a) b"
  by (metis gyr_master' gyr_even gyro_inv_idem)

text \<open>(3.52a)\<close>
lemma gyr_master_misc1':
  shows "gyr (\<ominus> a) b = gyr (\<ominus> (a \<oplus> a)) (a \<oplus> b) \<circ> gyr a b"
  by (metis fun.map_id gyr_master' local.gyr_id)

text \<open>(3.52b)\<close>
lemma gyr_master_misc1'':
  shows "gyr (\<ominus> a) b = gyr a b \<circ> gyr (b \<oplus> a) (\<ominus> (b \<oplus> b))"
  by (metis comp_id gyr_master gyr_id)

text \<open>(3.53a)\<close>
lemma gyr_master_misc2':
  shows "gyr (\<ominus>a \<oplus> b) (a \<oplus> b) = gyr (\<ominus> a) b \<circ> gyr b a"
  by (simp add: gyr_commute_misc_4'')

text \<open>(3.53b)\<close>
lemma gyr_master_misc2'':
  shows "gyr (\<ominus>a \<oplus> b) (a \<oplus> b) = gyr (\<ominus> a \<oplus> b) b \<circ> gyr b (a \<oplus> b)"
  using gyr_master_misc2' local.gyr_left_loop local.gyr_right_loop
  by auto


text \<open>Thm 3.18 (3.60)\<close>
lemma "gyr a x \<circ> gyr (\<ominus> (gyr x a (a \<ominus>\<^sub>b b))) (x \<oplus> b) \<circ> gyr x b = gyr a (\<ominus> b)"
  by (metis gyr_master gyro_translation_2b gyr_even gyr_left_loop gyro_inv_idem gyrominus_def)

definition gyro_covariant :: "nat \<Rightarrow> ('a list \<Rightarrow> 'a) \<Rightarrow> bool" where
  "gyro_covariant n T \<longleftrightarrow> (\<forall> \<tau> xs. length xs = n \<and> gyroaut \<tau> \<longrightarrow> (\<tau> (T xs)) = T (map \<tau> xs)) \<and> 
                        (\<forall> x xs. length xs = n \<longrightarrow> x \<oplus> T xs = T (map (\<lambda> a. x \<oplus> a) xs))"

definition gyro_covariant_3 :: "('a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "gyro_covariant_3 T \<longleftrightarrow> (\<forall> \<tau> a b c. gyroaut \<tau> \<longrightarrow> (\<tau> (T a b c)) = T (\<tau> a) (\<tau> b) (\<tau> c)) \<and> 
                          (\<forall> x a b c. x \<oplus> T a b c = T (x \<oplus> a) (x \<oplus> b) (x \<oplus> c))"

lemma gyro_covariant_3: 
  shows "gyro_covariant_3 T \<longleftrightarrow> gyro_covariant 3 (\<lambda> xs. T (xs ! 0) (xs ! 1) (xs ! 2))"
  unfolding gyro_covariant_3_def gyro_covariant_def
  apply safe
     apply simp
    apply simp
   apply (erule_tac x="\<tau>" in allE, erule_tac x="[a, b, c]" in allE, simp)
  apply (erule_tac x="x" in allE, erule_tac x="[a, b, c]" in allE, simp)
  done

text \<open>Thm 3.19 (3.62)\<close>
lemma gyro_covariant_3_parallelogram:                
  shows "gyro_covariant_3 (\<lambda> a b c. (b \<oplus>\<^sub>c c) \<ominus>\<^sub>b a)"  
  unfolding gyro_covariant_3_def
proof safe
  fix \<tau> a b c
  assume "gyroaut \<tau>"
  then show "\<tau> ((b \<oplus>\<^sub>c c) \<ominus>\<^sub>b a) = (\<tau> b \<oplus>\<^sub>c \<tau> c) \<ominus>\<^sub>b \<tau> a"
    by (smt (verit, ccfv_threshold) cogyroaut_def gyro_coaut_iff_gyro_aut local.gyro_left_cancel' local.gyro_left_inv local.gyroaut_def local.gyrominus_def)
next
  fix x a b c
  have "((x \<oplus> b) \<oplus>\<^sub>c (x \<oplus> c)) \<ominus>\<^sub>b (x \<oplus> a) = (x \<oplus> b) \<oplus> gyr (x \<oplus> b) (\<ominus> (x \<oplus> c)) ((x \<oplus> c) \<ominus>\<^sub>b (x \<oplus> a))"
    by (simp add: gyrominus_def mixed_gyroassoc_law)
  also have "... = (x \<oplus> b) \<oplus> gyr (x \<oplus> b) (\<ominus> (x \<oplus> c)) (gyr x c (c \<ominus>\<^sub>b a))"
    by (simp add: gyro_translation_2b)
  also have "... = x \<oplus> (b \<oplus> gyr b x (gyr (x \<oplus> b) (\<ominus> (x \<oplus> c)) (gyr x c (c \<ominus>\<^sub>b a))))"
    using local.gyro_right_assoc by auto
  also have "... = x \<oplus> (b \<oplus> gyr b x (gyr x b (gyr b (\<ominus> c) (gyr c x (gyr x c (c \<ominus>\<^sub>b a))))))"
    unfolding gyrominus_def
    using gyro_commute_misc_4[of "\<ominus> x" b c]
    by (simp add: gyroautomorphic_inverse local.gyr_even)
  also have "... = x \<oplus> (b \<oplus> gyr b (\<ominus> c) (c \<ominus>\<^sub>b a))"
    by (metis local.gyr_auto_id2 local.gyr_right_loop pointfree_idE)
  finally show "x \<oplus> ((b \<oplus>\<^sub>c c) \<ominus>\<^sub>b a) = ((x \<oplus> b) \<oplus>\<^sub>c (x \<oplus> c)) \<ominus>\<^sub>b (x \<oplus> a)"
    using gyrominus_def mixed_gyroassoc_law 
    by auto
qed

lemma gyro_commute_misc6':
  shows "x \<oplus> ((b \<oplus>\<^sub>c c) \<ominus>\<^sub>b a) = ((x \<oplus> b) \<oplus>\<^sub>c (x \<oplus> c)) \<ominus>\<^sub>b (x \<oplus> a)"
  using gyro_covariant_3_parallelogram
  unfolding gyro_covariant_3_def
  by simp
  
text \<open>(3.66)\<close>
lemma gyro_commute_misc6:
  shows "(x \<oplus> b) \<oplus>\<^sub>c (x \<oplus> c) = x \<oplus> ((b \<oplus>\<^sub>c c) \<oplus> x)"
  using gyro_commute_misc6'[of x b c "\<ominus> x"]
  by (simp add: gyrominus_def)

text \<open>(3.67)\<close>
lemma gyro_commute_misc6'':
  shows "(x \<oplus> b) \<oplus>\<^sub>c (x \<ominus>\<^sub>b b) = x \<oplus> x"
  using gyro_commute_misc6 cogyro_gyro_inv cogyro_right_inv gyro_left_id gyrominus_def 
  by presburger

end

type_synonym 'a rooted_gyrovec = "'a \<times> 'a"

context gyrogroup
begin

text \<open>Def 5.2.\<close>
fun head :: "'a rooted_gyrovec \<Rightarrow> 'a" where
  "head (p, q) = q"
fun tail :: "'a rooted_gyrovec \<Rightarrow> 'a" where
  "tail (p, q) = p"
fun val :: "'a rooted_gyrovec \<Rightarrow> 'a" where
  "val (p, q) = \<ominus> p \<oplus> q"
definition ort :: "'a \<Rightarrow> 'a rooted_gyrovec" where
  "ort p = (0\<^sub>g, p)"

fun equiv_rooted_gyro_vec (infixl "\<sim>" 100) where
  "(p, q) \<sim> (p', q') \<longleftrightarrow> \<ominus>p \<oplus> q = \<ominus>p' \<oplus> q'"

lemma equivp_equiv_rooted_gyro_vec [simp]:
  shows "equivp (\<sim>)"
  unfolding equivp_def
  by fastforce

end

text \<open>Def 5.4.\<close>
quotient_type (overloaded) 'a gyrovec = "'a :: gyrogroup \<times> 'a" / equiv_rooted_gyro_vec
  by auto
                  
lift_definition vec :: "'a::gyrogroup \<Rightarrow> 'a \<Rightarrow> 'a gyrovec" is "\<lambda> p q. (p, q)" .

definition ort :: "'a::gyrogroup \<Rightarrow> 'a gyrovec" where
  "ort A = vec 0\<^sub>g A"

context gyrocommutative_gyrogroup
begin

text \<open>Thm 5.5. (5.4)\<close>
lemma equiv_rooted_gyro_vec_ex_t:
  shows "(p, q) \<sim> (p', q') \<longleftrightarrow> (\<exists> t. p' = gyr p t (t \<oplus> p) \<and> q' = gyr p t (t \<oplus> q))" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  let ?t = "\<ominus>p \<oplus> p'"

  have "\<ominus>(?t \<oplus> p) \<oplus> (?t \<oplus> q) = gyr ?t p (\<ominus>p \<oplus> q)"
    by (metis gyr_def gyro_equation_right)

  hence "\<ominus>p \<oplus> q = gyr (\<ominus> p) (\<ominus> ?t) (\<ominus>(?t \<oplus> p) \<oplus> (?t \<oplus> q))"
    by (metis gyr_aut_inv_2 gyr_auto_id1 gyr_even inv_gyr_sym pointfree_idE)
  hence "\<ominus>p \<oplus> q = gyr p ?t (\<ominus>(?t \<oplus> p) \<oplus> (?t \<oplus> q))"
    using gyr_even by presburger

  show ?thesis
  proof
    assume "(p, q) \<sim> (p', q')"
    hence *: "\<ominus>p \<oplus> q = \<ominus>p' \<oplus> q'"
      by simp

    have "p' = gyr p ?t (?t \<oplus> p)" 
      using *
      using gyro_commute gyro_equation_right gyro_left_cancel by blast

    moreover

    have "q' = gyr p ?t (?t \<oplus> q)"
    proof-
      have "q' = p' \<oplus> (\<ominus> p \<oplus> q)"
        by (metis "*" gyro_left_cancel')
      also have "... = gyr p ?t (?t \<oplus> p) \<oplus> (\<ominus> p \<oplus> q)"
        using \<open>p' = gyr p (\<ominus> p \<oplus> p') (\<ominus> p \<oplus> p' \<oplus> p)\<close> 
        by auto
      also have "... = (gyr p ?t ?t \<oplus> gyr p ?t p) \<oplus> (\<ominus> p \<oplus> q)"
        by simp
      also have "... = gyr p ?t ?t \<oplus> (gyr p ?t p \<oplus> gyr (gyr p ?t p) (gyr p ?t ?t) (\<ominus> p \<oplus> q))"
        using gyro_right_assoc by blast
      also have "... = gyr p ?t ?t \<oplus> (gyr p ?t p \<oplus> gyr p ?t (\<ominus> p \<oplus> q))"
        using gyr_commute_misc_1
        by presburger
      also have "... = gyr p ?t ?t \<oplus> gyr p ?t q"
        by (metis gyr_distrib gyro_equation_right)
      finally show "q' = gyr p ?t (?t \<oplus> q)"
        by simp
    qed

    ultimately

    show ?rhs
      by blast

  next

    assume ?rhs
    then obtain t where t: "p' = gyr p t (t \<oplus> p) \<and> q' = gyr p t (t \<oplus> q)"
      by auto

    have "\<ominus> p \<oplus> q = gyr p t (\<ominus> (t \<oplus> p) \<oplus> (t \<oplus> q))"
      by (metis gyro_left_assoc gyro_left_cancel gyro_right_assoc gyro_translation_2a)
    also have "... = \<ominus> (gyr p t (t \<oplus> p)) \<oplus> gyr p t (t \<oplus> q)"
      by (simp add: gyr_inv_3)
    finally show ?lhs
      using t
      by auto
  qed
qed

text \<open>Thm 5.5. (5.5)\<close>
lemma gyro_translate_commute:
  assumes "p' = gyr p t (t \<oplus> p) \<and> q' = gyr p t (t \<oplus> q)"
  shows "t = \<ominus>p \<oplus> p'"
  using assms
  using gyro_commute gyro_equation_right by blast

text \<open>Def 5.6.\<close>
fun gyrovec_translation :: "'a \<Rightarrow> 'a rooted_gyrovec \<Rightarrow> 'a rooted_gyrovec" where
  "gyrovec_translation t (p, q) = (gyr p t (t \<oplus> p), gyr p t (t \<oplus> q))"
end

lift_definition gyrovec_translation' :: "('a::gyrocommutative_gyrogroup) gyrovec \<Rightarrow> 'a rooted_gyrovec \<Rightarrow> 'a rooted_gyrovec" is 
  "\<lambda> (tp, tq) (p, q). gyrovec_translation (\<ominus> tp \<oplus> tq) (p, q)"
  by force

text \<open>(5.14)\<close>
lemma
  shows "tail (gyrovec_translation t (p, q)) = p \<oplus> t"
  by (metis gyrovec_translation.simps gyro_commute tail.simps)

text \<open>(5.15)\<close>
lemma gyrovec_translation_id:
  shows "gyrovec_translation 0\<^sub>g (p, q) = (p, q)"
  by simp

text \<open>Thm 5.7.\<close>
lemma equiv_rooted_gyrovec_t:
  shows "(p, q) \<sim> (p', q') \<longleftrightarrow> (p', q') = gyrovec_translation (\<ominus>p \<oplus> p') (p, q)"
  using equiv_rooted_gyro_vec_ex_t gyro_translate_commute
  by (metis gyrovec_translation.simps)

text \<open>Thm 5.8.\<close>
lemma gyrovec_translation_head:
  assumes "(p', x) = gyrovec_translation t (p, q)"  
  shows "x = p' \<oplus> (\<ominus>p \<oplus> q)"
  by (metis assms equiv_rooted_gyro_vec_ex_t gyrovec_translation.simps equiv_rooted_gyro_vec.simps gyro_equation_right)

text \<open>(5.24)\<close>

context gyrocommutative_gyrogroup
begin

definition gyrovec_translation_inv' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "gyrovec_translation_inv' p t = \<ominus> (gyr p t t)"

lemma gyrovec_translation_inv':
  shows "gyrovec_translation (gyrovec_translation_inv' p t) (gyrovec_translation t (p, q)) = (p, q)"
  unfolding gyrovec_translation_inv'_def
proof -
  have f1: "\<forall>a aa. gyr (aa::'a) a (a \<oplus> aa) = aa \<oplus> a"
    by (metis (no_types) cogyro_commute cogyro_commute_iff_gyrocommute)
  have "\<forall>a aa. \<ominus> (gyr (aa::'a) a a) = \<ominus> (aa \<oplus> a) \<oplus> aa"
    by (simp add: gyr_misc_3)
  then have "\<forall>a aa ab. (ab::'a, ab \<oplus> (\<ominus> (ab \<oplus> aa) \<oplus> a)) = gyrovec_translation (\<ominus> (gyr ab aa aa)) (ab \<oplus> aa, a)"
    using f1 by (metis gyrovec_translation.simps gyr_commute_misc_3 gyro_left_cancel')
  then have "\<forall>a aa ab. gyrovec_translation (\<ominus> (gyr (ab::'a) aa aa)) (gyrovec_translation aa (ab, a)) = (ab, a)"
    using f1 by (metis gyrovec_translation.simps gyr_commute_misc_3 gyro_left_cancel')
  then show "gyrovec_translation (\<ominus> (gyr p t t)) (gyrovec_translation t (p, q)) = (p, q)"
    by blast
qed

definition gyrovec_translation_compose' :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "gyrovec_translation_compose' p t1 t2 = t1 \<oplus> gyr t1 p t2"

lemma gyrovec_translation_compose':
  "gyrovec_translation t2 (gyrovec_translation t1 (p, q)) =
        gyrovec_translation (gyrovec_translation_compose' p t1 t2) (p, q)"
  by (smt (verit) comp_eq_dest_lhs gyrovec_translation_compose'_def local.gyr_auto_id2 local.gyr_commute_misc_3 local.gyr_distrib local.gyr_nested_1 local.gyr_right_loop local.gyro_commute local.gyro_right_assoc local.gyrovec_translation.simps pointfree_idE prod.inject)

fun equiv_translate (infixl "~\<^sub>t" 100) where
  "(p1, q1) ~\<^sub>t (p2, q2) \<longleftrightarrow> (\<exists> t. gyrovec_translation t (p1, q1) = (p2, q2))"

lemma equivp_equiv_translate:
  "equivp (~\<^sub>t)"
proof (rule equivpI)
  show "reflp (~\<^sub>t)"
  proof
    fix x
    show "x ~\<^sub>t x"
      by (metis equiv_translate.elims(3) gyr_commute_misc_3 gyr_id_2 gyro_left_id gyrovec_translation.simps)
  qed
next
  show "symp (~\<^sub>t)"
  proof
    fix a b
    assume "a ~\<^sub>t b"
    thus "b ~\<^sub>t a"
      using gyrovec_translation_inv' 
      by (cases a, cases b, fastforce)
  qed
next
  show "transp (~\<^sub>t)"
  proof
    fix x y z
    assume "x ~\<^sub>t y" "y ~\<^sub>t z"
    thus "x ~\<^sub>t z"
      using gyrovec_translation_compose'
      by (cases x, cases y, cases z, fastforce)
  qed
qed

text \<open>(5.39)\<close>
definition vec :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "vec a b = \<ominus> a \<oplus> b"

text \<open>(5.40)\<close>
lemma "vec 0\<^sub>g b = b"
  by (simp add: vec_def)

text \<open>(5.41)\<close>
lemma
  assumes "vec a b = v" 
  shows "b = a \<oplus> v"
  by (metis assms local.gyro_left_cancel' local.vec_def)

text \<open>(5.42)\<close>
lemma
  "(a \<oplus> v) \<oplus> u = a \<oplus> (v \<oplus> gyr v a u)"
  by (rule gyro_right_assoc)

text \<open>(5.43)\<close>
lemma
  assumes "vec a b = v"
  shows "a = \<ominus>v \<oplus>\<^sub>c b"
  using assms
  using cogyro_commute cogyrominus_def gyro_equation_left gyro_left_cancel' vec_def
  by force

lemma
  shows "(\<ominus> a \<oplus> b) \<oplus> gyr (\<ominus>a) b (\<ominus> b \<oplus> c) = \<ominus>a \<oplus> c"
  by (rule gyro_polygonal_addition_lemma)  


definition torsion_elem::"'a\<Rightarrow> bool" where
  "torsion_elem g \<longleftrightarrow> g\<oplus>g = 0\<^sub>g"

end

(*torsion_free two_divisible*)
class tf_tw_group = gyrocommutative_gyrogroup +
  assumes a1:"\<forall>a. torsion_elem a \<longrightarrow> a =  0\<^sub>g"
  assumes a2:"\<forall>a. \<exists>b. (b\<oplus>b = a)"
begin

text "T3.32"
lemma unique_half:
  shows "(a\<oplus>a = c \<and> b\<oplus>b = c) \<longrightarrow> a=b"
proof
  assume "(a\<oplus>a = c \<and> b\<oplus>b = c)"
  show "a=b"
  proof-
    have "a\<oplus>a = b\<oplus>b"
      by (simp add: \<open>a \<oplus> a = c \<and> b \<oplus> b = c\<close>)
    moreover have "\<ominus> b \<oplus> (a\<oplus>a) = \<ominus> b \<oplus> (b\<oplus>b)"
      by (simp add: \<open>a \<oplus> a = c \<and> b \<oplus> b = c\<close>)
    moreover have "\<ominus> b \<oplus> a  \<oplus> (gyr (\<ominus> b) a) a =b "
      by (metis \<open>a \<oplus> a = c \<and> b \<oplus> b = c\<close> local.gyro_left_assoc local.gyro_left_cancel')
    moreover have "\<ominus> b \<oplus> a = \<ominus> (\<ominus> b \<oplus> a)"
      by (metis calculation(3) local.gyro_plus_def_co local.gyro_right_cancel'_dual local.gyroautomorphic_inverse)
    moreover have "\<ominus> b \<oplus> a  \<oplus> ( \<ominus> b \<oplus> a) =  0\<^sub>g"
      by (metis calculation(4) local.gyro_rigth_inv)
    moreover have " torsion_elem (\<ominus> b \<oplus> a)"
      using calculation(5) local.torsion_elem_def by blast
    moreover have "( \<ominus> b \<oplus> a) = 0\<^sub>g"
      using a1
      using calculation(6) by blast
    ultimately show ?thesis 
      by (metis local.gyro_left_inv local.oplus_ominus_cancel)
  qed
qed

text "T3.33"
lemma unique_gyro_half:
  assumes "gh\<oplus>gh = g"
      "gyr_h \<oplus> gyr_h = gyr a b g"
    shows "gyr a b gh = gyr_h"
  by (metis assms(1) assms(2) local.gyr_distrib unique_half)

text "3.102"
lemma gh_minus:
  assumes "gh\<oplus>gh = \<ominus> g"
        "gh2\<oplus>gh2 = g"
      shows " \<ominus> gh2 = gh"
  by (metis assms(1) assms(2) local.gyroautomorphic_inverse local.gyrominus_def unique_half)

text "T3.34"
lemma gyration_exclusion:
  assumes "\<exists>g. g\<noteq> 0\<^sub>g"
  shows "\<forall>a b.  gyr a b \<noteq>  \<ominus> \<circ> id"
proof(rule ccontr)
  assume "\<not> (\<forall>a b.  gyr a b \<noteq>  \<ominus> \<circ> id)"
  have "\<exists>a b.( gyr a b =  \<ominus> \<circ> id)"
    using \<open>\<not> (\<forall>a b. gyr a b \<noteq> \<ominus> \<circ> id)\<close> by auto
  
  moreover obtain "a" "b" where "gyr a b  = \<ominus>  \<circ> id "
    using calculation by blast
  moreover obtain "bh" where "bh \<oplus> bh = b"
    using a2
    by blast
  moreover have "a \<oplus> (b \<ominus>\<^sub>b bh) = (a  \<oplus> b)  \<oplus> bh "
  proof-
    have "a \<oplus> (b \<ominus>\<^sub>b bh) =  (a  \<oplus> b) \<ominus>\<^sub>b  gyr a b bh "
      by (simp add: local.gyr_inv_3 local.gyro_left_assoc local.gyrominus_def)
    moreover obtain "gh" where "gh \<oplus> gh =  gyr a b b"
      using local.a2 by blast
    moreover have "a \<oplus> (b \<ominus>\<^sub>b bh) = (a  \<oplus> b) \<ominus>\<^sub>b  gh"
      using \<open>bh \<oplus> bh = b\<close> calculation(1) calculation(2) unique_gyro_half by blast
    ultimately show ?thesis 
      by (simp add: \<open>gyr a b = \<ominus> \<circ> id\<close> local.gyrominus_def) 
  qed
  moreover have "a \<oplus> (b \<ominus>\<^sub>b bh) = a  \<oplus> bh"
    using calculation(3) local.gyro_left_right_cancel by force
  moreover have "b =  0\<^sub>g"
    by (metis calculation(4) calculation(5) local.cogyro_gyro_inv local.cogyroinv_def local.gyro_equation_left local.gyro_equation_right)
  moreover have "gyr a b = id"
    by (simp add: calculation(6))
  moreover have "gyr a b  = \<ominus>  \<circ> id "
    using calculation(2) by blast
  ultimately show False
    by (metis assms comp_id id_def local.gyro_rigth_inv unique_gyro_half)
qed

text "T3.35"
lemma gyration_exclusion_cons:
  shows "gyr a b b =  \<ominus> b \<longrightarrow> b = 0\<^sub>g"
proof
  assume "gyr a b b =  \<ominus> b "
  show "b = 0\<^sub>g"
  proof-
   obtain "bh" where "bh \<oplus> bh = b"
    using a2
    by blast
  moreover have "a \<oplus> (b \<ominus>\<^sub>b bh) = (a  \<oplus> b)  \<oplus> bh "
  proof-
    have "a \<oplus> (b \<ominus>\<^sub>b bh) =  (a  \<oplus> b) \<ominus>\<^sub>b  gyr a b bh "
      by (simp add: local.gyr_inv_3 local.gyro_left_assoc local.gyrominus_def)
    moreover obtain "gh" where "gh \<oplus> gh =  gyr a b b"
      using local.a2 by blast
    moreover have "a \<oplus> (b \<ominus>\<^sub>b bh) = (a  \<oplus> b) \<ominus>\<^sub>b  gh"
      using \<open>bh \<oplus> bh = b\<close> calculation(1) calculation(2) unique_gyro_half by blast
    ultimately show ?thesis 
      by (metis \<open>bh \<oplus> bh = b\<close> \<open>gyr a b b = \<ominus> b\<close> gh_minus local.gyro_inv_idem local.gyrominus_def)
  qed
  moreover have "a \<oplus> (b \<ominus>\<^sub>b bh) = a  \<oplus> bh"
    using calculation(1) local.gyro_left_right_cancel by force
  ultimately show ?thesis 
    by (metis local.gyr_right_loop local.gyro_commute local.gyro_left_cancel local.gyro_right_id)
qed
qed

text "T3.36"
lemma equation_t3_36:
  shows " x  \<ominus>\<^sub>b (y  \<ominus>\<^sub>b x) = y \<longleftrightarrow> x = y"
  by (metis gyration_exclusion_cons local.gyr_commute_misc_3 local.gyr_misc_1 local.gyr_misc_3 local.gyro_right_id local.gyro_rigth_inv local.gyrominus_def)



end

locale gyrogroup_isomorphism = 
  fixes \<phi> :: "'a::gyrocommutative_gyrogroup \<Rightarrow> 'b" 
  fixes gyrozero' :: "'b" ("0\<^sub>g\<^sub>1")
  fixes gyroplus' :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "\<oplus>\<^sub>1" 100)
  fixes gyroinv' :: "'b \<Rightarrow> 'b" ("\<ominus>\<^sub>1")
  assumes \<phi>zero [simp]: "\<phi> 0\<^sub>g = 0\<^sub>g\<^sub>1"
  assumes \<phi>plus [simp]: "\<phi> (a \<oplus> b) = (\<phi> a) \<oplus>\<^sub>1 (\<phi> b)"
  assumes \<phi>minus [simp]: "\<phi> (\<ominus> a) = \<ominus>\<^sub>1 (\<phi> a)"
  assumes \<phi>bij [simp]: "bij \<phi>"
begin

definition gyr' where
 "gyr' a b x = \<ominus>\<^sub>1 (a \<oplus>\<^sub>1 b) \<oplus>\<^sub>1 (a \<oplus>\<^sub>1 (b \<oplus>\<^sub>1 x))"

lemma \<phi>gyr [simp]:
  shows "\<phi> (gyr a b z) = gyr' (\<phi> a) (\<phi> b) (\<phi> z)"
  by (simp add: gyr'_def gyr_def)

end

sublocale gyrogroup_isomorphism \<subseteq> gyrogroupoid gyrozero' gyroplus'
  by unfold_locales

sublocale gyrogroup_isomorphism \<subseteq> gyrocommutative_gyrogroup gyrozero' gyroplus' gyroinv' gyr'
proof
  fix a
  show "0\<^sub>g\<^sub>1 \<oplus>\<^sub>1 a = a"
    by (metis \<phi>bij \<phi>plus \<phi>zero bij_iff gyro_left_id)
next
  fix a
  show "\<ominus>\<^sub>1 a \<oplus>\<^sub>1 a = 0\<^sub>g\<^sub>1"
    by (metis \<phi>bij \<phi>minus \<phi>plus \<phi>zero bij_iff gyro_left_inv)
next
  fix a b z
  show "a \<oplus>\<^sub>1 (b \<oplus>\<^sub>1 z) = a \<oplus>\<^sub>1 b \<oplus>\<^sub>1 gyr' a b z"
    using \<phi>gyr[of "inv \<phi> a" "inv \<phi> b" "inv \<phi> z"]
    by (metis \<phi>bij \<phi>plus bij_inv_eq_iff gyro_left_assoc)
next
  fix a b
  show "gyr' a b = gyr' (a \<oplus>\<^sub>1 b) b"
  proof
    fix z
    show "gyr' a b z = gyr' (a \<oplus>\<^sub>1 b) b z"
      using \<phi>gyr[of "inv \<phi> a" "inv \<phi> b" "inv \<phi> z"]
      by (smt (z3) \<phi>bij \<phi>gyr \<phi>plus bij_inv_eq_iff gyr_aut_inv_3 inv_gyr_sym)
  qed
next
  fix a b
  have *: "gyr' a b = \<phi> \<circ> (gyr (inv \<phi> a) (inv \<phi> b)) \<circ> (inv \<phi>)"
  proof
    fix z
    show "gyr' a b z = (\<phi> \<circ> gyr (inv \<phi> a) (inv \<phi> b) \<circ> inv \<phi>) z"
      by (metis \<phi>bij \<phi>gyr bij_inv_eq_iff comp_def)
  qed
  show "gyroaut (gyr' a b)"
    unfolding gyroaut_def
  proof safe
    show "bij (gyr' a b)"
      using * \<phi>bij gyr_gyroaut
      by (metis bij_comp bij_imp_bij_inv gyrogroupoid_class.gyroaut_def)
  next
    fix x y
    show "gyr' a b (x \<oplus>\<^sub>1 y) = gyr' a b x \<oplus>\<^sub>1 gyr' a b y"
      using *
      by (smt (verit, del_insts) \<phi>bij \<phi>plus bij_inv_eq_iff comp_def gyr_distrib)
  qed
next
  fix a b
  show "a \<oplus>\<^sub>1 b = gyr' a b (b \<oplus>\<^sub>1 a)"
    using \<phi>gyr[of "inv \<phi> a" "inv \<phi> b" "inv \<phi> (b \<oplus>\<^sub>1 a)"]
    by (metis (no_types, lifting) \<phi>bij \<phi>plus bij_inv_eq_iff gyro_commute)
qed

end
