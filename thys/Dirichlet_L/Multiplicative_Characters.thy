(*
    File:      Multiplicative_Characters.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>Multiplicative Characters of Finite Abelian Groups\<close>
theory Multiplicative_Characters
imports
  Complex_Main
  Group_Adjoin
begin

subsection \<open>Definition of characters\<close>

text \<open>
  A (multiplicative) character is a completely multiplicative function from a group to the
  complex numbers. For simplicity, we restrict this to finite abelian groups here, which is
  the most interesting case.

  Characters form a group where the identity is the \emph{principal} character that maps all
  elements to $1$, multiplication is point-wise multiplication of the characters, and the inverse
  is the point-wise complex conjugate.

  This group is often called the \emph{dual} group and is isomorphic to the original group
  (in a non-natural way) and the double-dual group is naturally isomorphic to the original group.
  However, we do not show these last few facts here since we do not need them for the Dirichlet
  $L$-functions.

  To get extensionality of the characters, we also require characters to map anything that is
  not in the group to $0$.
\<close>

definition principal_char :: "('a, 'b) monoid_scheme \<Rightarrow> 'a \<Rightarrow> complex" where
  "principal_char G a = (if a \<in> carrier G then 1 else 0)"

definition inv_character where
  "inv_character \<chi> = (\<lambda>a. cnj (\<chi> a))"

lemma inv_character_principal [simp]: "inv_character (principal_char G) = principal_char G"
  by (simp add: inv_character_def principal_char_def fun_eq_iff)

lemma inv_character_inv_character [simp]: "inv_character (inv_character \<chi>) = \<chi>"
  by (simp add: inv_character_def)

lemma eval_inv_character: "inv_character \<chi> j = cnj (\<chi> j)"
  by (simp add: inv_character_def)


bundle character_syntax
begin
notation principal_char ("\<chi>\<^sub>0\<index>")
end

locale character = finite_comm_group +
  fixes \<chi> :: "'a \<Rightarrow> complex"
  assumes char_one_nz: "\<chi> \<one> \<noteq> 0"
  assumes char_eq_0:   "a \<notin> carrier G \<Longrightarrow> \<chi> a = 0"
  assumes char_mult [simp]: "a \<in> carrier G \<Longrightarrow> b \<in> carrier G \<Longrightarrow> \<chi> (a \<otimes> b) = \<chi> a * \<chi> b"
begin


subsection \<open>Basic properties\<close>

lemma char_one [simp]: "\<chi> \<one> = 1"
proof-
  from char_mult[of \<one> \<one>] have "\<chi> \<one> * (\<chi> \<one> - 1) = 0"
    by (auto simp del: char_mult)
  with char_one_nz show ?thesis by simp
qed

lemma char_power [simp]: "a \<in> carrier G \<Longrightarrow> \<chi> (a (^) k) = \<chi> a ^ k"
  by (induction k) auto

lemma char_root:
  assumes "a \<in> carrier G"
  shows   "\<chi> a ^ ord a = 1"
proof -
  from assms have "\<chi> a ^ ord a = \<chi> (a (^) ord a)" by simp
  also from fin and assms have "a (^) ord a = \<one>" by (intro pow_ord_eq_1) auto
  finally show ?thesis by simp
qed

lemma char_root':
  assumes "a \<in> carrier G"
  shows   "\<chi> a ^ order G = 1"
proof -
  from assms have "\<chi> a ^ order G = \<chi> (a (^) order G)" by simp
  also from fin and assms have "a (^) order G = \<one>" by (intro pow_order_eq_1) auto
  finally show ?thesis by simp
qed

lemma norm_char: "norm (\<chi> a) = (if a \<in> carrier G then 1 else 0)"
proof (cases "a \<in> carrier G")
  case True
  have "norm (\<chi> a) ^ order G = norm (\<chi> a ^ order G)" by (simp add: norm_power)
  also from True have "\<chi> a ^ order G = 1" by (rule char_root')
  finally have "norm (\<chi> a) ^ order G = 1 ^ order G" by simp
  hence "norm (\<chi> a) = 1" by (subst (asm) power_eq_iff_eq_base) auto
  with True show ?thesis by auto
next
  case False
  thus ?thesis by (auto simp: char_eq_0)
qed

lemma char_eq_0_iff: "\<chi> a = 0 \<longleftrightarrow> a \<notin> carrier G"
proof -
  have "\<chi> a = 0 \<longleftrightarrow> norm (\<chi> a) = 0" by simp
  also have "\<dots> \<longleftrightarrow> a \<notin> carrier G" by (subst norm_char) auto
  finally show ?thesis .
qed

lemma inv_character: "character G (inv_character \<chi>)"
  by standard (auto simp: inv_character_def char_eq_0)

lemma mult_inv_character: "\<chi> k * inv_character \<chi> k = principal_char G k"
proof -
  have "\<chi> k * inv_character \<chi> k = of_real (norm (\<chi> k) ^ 2)"
    by (subst complex_norm_square) (simp add: inv_character_def)
  also have "\<dots> = principal_char G k"
    by (simp add: principal_char_def norm_char)
  finally show ?thesis .
qed

lemma
  assumes "a \<in> carrier G"
  shows    char_inv: "\<chi> (inv a) = cnj (\<chi> a)" and char_inv': "\<chi> (inv a) = inverse (\<chi> a)"
proof -
  from assms have "inv a \<otimes> a = \<one>" by simp
  also have "\<chi> \<dots> = 1" by simp
  also from assms have "\<chi> (inv a \<otimes> a) = \<chi> (inv a) * \<chi> a"
    by (intro char_mult) auto
  finally have *: "\<chi> (inv a) * \<chi> a = 1" .
  thus "\<chi> (inv a) = inverse (\<chi> a)" by (auto simp: divide_simps)
  also from mult_inv_character[of a] and assms have "inverse (\<chi> a) = cnj (\<chi> a)"
    by (auto simp add: inv_character_def principal_char_def divide_simps mult.commute)
  finally show "\<chi> (inv a) = cnj (\<chi> a)" .
qed

end

lemma (in finite_comm_group) character_principal [simp, intro]: "character G (principal_char G)"
  by standard (auto simp: principal_char_def)

lemmas [simp,intro] = finite_comm_group.character_principal

lemma character_mult [intro]: 
  assumes "character G \<chi>" "character G \<chi>'"
  shows   "character G (\<lambda>x. \<chi> x * \<chi>' x)"
proof -
  interpret \<chi>: character G \<chi> by fact
  interpret \<chi>': character G \<chi>' by fact
  show ?thesis by standard (auto simp: \<chi>.char_eq_0)
qed
 

lemma character_inv_character_iff [simp]: "character G (inv_character \<chi>) \<longleftrightarrow> character G \<chi>"
proof
  assume "character G (inv_character \<chi>)"
  from character.inv_character [OF this] show "character G \<chi>" by simp
qed (auto simp: character.inv_character)


definition characters :: "('a, 'b) monoid_scheme \<Rightarrow> ('a \<Rightarrow> complex) set"  where
  "characters G = {\<chi>. character G \<chi>}"

definition Characters :: "('a, 'b) monoid_scheme \<Rightarrow> ('a \<Rightarrow> complex) monoid" 
  where "Characters G = \<lparr> carrier = characters G, mult = (\<lambda>\<chi>\<^sub>1 \<chi>\<^sub>2 k. \<chi>\<^sub>1 k * \<chi>\<^sub>2 k),
                          one = principal_char G \<rparr>"

lemma carrier_Characters: "carrier (Characters G) = characters G"
  by (simp add: Characters_def)

lemma one_Characters: "one (Characters G) = principal_char G"
  by (simp add: Characters_def)

lemma mult_Characters: "mult (Characters G) \<chi>\<^sub>1 \<chi>\<^sub>2 = (\<lambda>a. \<chi>\<^sub>1 a * \<chi>\<^sub>2 a)"
  by (simp add: Characters_def)

context finite_comm_group
begin

sublocale principal: character G "principal_char G" ..

lemma finite_characters [intro]: "finite (characters G)"
proof (rule finite_subset)
  show "characters G \<subseteq> (\<lambda>f x. if x \<in> carrier G then f x else 0) ` 
                          Pi\<^sub>E (carrier G) (\<lambda>_. {z. z ^ order G = 1})" (is "_ \<subseteq> ?h ` ?Chars")
  proof (intro subsetI, goal_cases)
    case (1 \<chi>)
    then interpret \<chi>: character G \<chi> by (simp add: characters_def)
    have "?h (restrict \<chi> (carrier G)) \<in> ?h ` ?Chars"
      by (intro imageI) (auto simp: \<chi>.char_root')
    also have "?h (restrict \<chi> (carrier G)) = \<chi>" by (simp add: fun_eq_iff \<chi>.char_eq_0)
    finally show ?case .
  qed
  show "finite (?h ` ?Chars)"
    by (intro finite_imageI finite_PiE finite_roots_unity) (auto simp: Suc_le_eq)
qed

text \<open>
  Characters form a group.
\<close>
lemma finite_comm_group_Characters [intro]: "finite_comm_group (Characters G)"
proof
  fix \<chi> \<chi>' assume *: "\<chi> \<in> carrier (Characters G)" "\<chi>' \<in> carrier (Characters G)"
  from * interpret \<chi>: character G \<chi> by (simp_all add: characters_def carrier_Characters)
  from * interpret \<chi>': character G \<chi>' by (simp_all add: characters_def  carrier_Characters)
  have "character G (\<lambda>k. \<chi> k * \<chi>' k)"
    by standard (insert *, simp_all add: \<chi>.char_eq_0 one_Characters 
                                         mult_Characters characters_def  carrier_Characters)
  thus "\<chi> \<otimes>\<^bsub>Characters G\<^esub> \<chi>' \<in> carrier (Characters G)"
    by (simp add: characters_def one_Characters mult_Characters  carrier_Characters)
next
  have "character G (principal_char G)" ..
  thus "\<one>\<^bsub>Characters G\<^esub> \<in> carrier (Characters G)"
    by (simp add: characters_def one_Characters mult_Characters  carrier_Characters)
next
  fix \<chi> assume *: "\<chi> \<in> carrier (Characters G)"
  from * interpret \<chi>: character G \<chi> by (simp_all add: characters_def carrier_Characters)
  show "\<one>\<^bsub>Characters G\<^esub> \<otimes>\<^bsub>Characters G\<^esub> \<chi> = \<chi>" and "\<chi> \<otimes>\<^bsub>Characters G\<^esub> \<one>\<^bsub>Characters G\<^esub> = \<chi>"
    by (simp_all add: principal_char_def fun_eq_iff \<chi>.char_eq_0 one_Characters mult_Characters)
next
  have "\<chi> \<in> Units (Characters G)" if "\<chi> \<in> carrier (Characters G)" for \<chi>
  proof -
    from that interpret \<chi>: character G \<chi> by (simp add: characters_def carrier_Characters)
    have "\<chi> \<otimes>\<^bsub>Characters G\<^esub> inv_character \<chi> = \<one>\<^bsub>Characters G\<^esub>" and 
         "inv_character \<chi> \<otimes>\<^bsub>Characters G\<^esub> \<chi> = \<one>\<^bsub>Characters G\<^esub>"
      by (simp_all add: \<chi>.mult_inv_character mult_ac one_Characters mult_Characters)
    moreover from that have "inv_character \<chi> \<in> carrier (Characters G)"
      by (simp add: characters_def carrier_Characters)
    ultimately show ?thesis using that unfolding Units_def by blast
  qed
  thus "carrier (Characters G) \<subseteq> Units (Characters G)" ..
qed (auto simp: principal_char_def one_Characters mult_Characters carrier_Characters)

end

lemma (in character) character_in_order_1:
  assumes "order G = 1"
  shows   "\<chi> = principal_char G"
proof -
  from assms have "card (carrier G - {\<one>}) = 0"
    by (subst card_Diff_subset) (auto simp: order_def)
  hence "carrier G - {\<one>} = {}"
    by (subst (asm) card_0_eq) auto
  hence "carrier G = {\<one>}" by auto
  thus ?thesis
    by (intro ext) (simp_all add: principal_char_def char_eq_0)
qed

lemma (in finite_comm_group) characters_in_order_1:
  assumes "order G = 1"
  shows   "characters G = {principal_char G}"
  using character.character_in_order_1 [OF _ assms] by (auto simp: characters_def)

lemma (in character) inv_Characters: "inv\<^bsub>Characters G\<^esub> \<chi> = inv_character \<chi>"
proof -
  interpret Characters: finite_comm_group "Characters G" ..
  have "character G \<chi>" ..
  thus ?thesis
    by (intro Characters.inv_equality) 
       (auto simp: characters_def mult_inv_character mult_ac 
                   carrier_Characters one_Characters mult_Characters)
qed

lemma (in finite_comm_group) inv_Characters': 
  "\<chi> \<in> characters G \<Longrightarrow> inv\<^bsub>Characters G\<^esub> \<chi> = inv_character \<chi>"
  by (intro character.inv_Characters) (auto simp: characters_def)

lemma inv_Characters': "\<chi> \<in> characters G \<Longrightarrow> inv\<^bsub>Characters G\<^esub> \<chi> = inv_character \<chi>"
  using character.inv_Characters[of G \<chi>] by (simp add: characters_def)



subsection \<open>Relationship of characters and adjoining\<close>

context finite_comm_group_adjoin
begin

lemma lower_character:
  assumes "character (G\<lparr>carrier := adjoin G H a\<rparr>) \<chi>" 
    (is "character ?G'' _")
  shows   "character (G\<lparr>carrier := H\<rparr>) (\<lambda>x. if x \<in> H then \<chi> x else 0)" (is "character ?G' ?\<chi>")
proof -
  have "subgroup H G" ..
  then interpret G'': finite_comm_group ?G'' 
    by (intro subgroup_imp_finite_comm_group adjoin_subgroup) auto
  from \<open>subgroup H G\<close> interpret G': finite_comm_group ?G'
    by (intro subgroup_imp_finite_comm_group adjoin_subgroup) auto
  from assms interpret character ?G'' \<chi>
    by (simp add: characters_def)
  show ?thesis
  proof
    fix x y assume "x \<in> carrier ?G'" "y \<in> carrier ?G'"
    thus "?\<chi> (x \<otimes>\<^bsub>?G'\<^esub> y) = ?\<chi> x * ?\<chi> y"
      using char_mult[of x y] mem_adjoin[OF \<open>subgroup H G\<close>] by auto
  qed (insert char_one, auto simp del: char_one)
qed

definition lift_character :: "('a \<Rightarrow> complex) \<times> complex \<Rightarrow> ('a \<Rightarrow> complex)" where
  "lift_character = 
     (\<lambda>(\<chi>,z) x. if x \<in> adjoin G H a then \<chi> (fst (unadjoin x)) * z ^ snd (unadjoin x) else 0)"

lemma lift_character:
  defines "h \<equiv> subgroup_indicator G H a"
  assumes "character (G\<lparr>carrier := H\<rparr>) \<chi>" (is "character ?G' _") and "z ^ h = \<chi> (a (^) h)"
  shows   "character (G\<lparr>carrier := adjoin G H a\<rparr>) (lift_character (\<chi>, z))" (is "character ?G'' _")
proof -
  interpret H': subgroup "adjoin G H a" G by (intro adjoin_subgroup is_subgroup) auto
  have "subgroup H G" ..
  then interpret G'': finite_comm_group ?G''
    by (intro subgroup_imp_finite_comm_group adjoin_subgroup) auto
  from \<open>subgroup H G\<close> interpret G': finite_comm_group ?G'
    by (intro subgroup_imp_finite_comm_group adjoin_subgroup) auto
  from assms interpret character ?G' \<chi> by (simp add: characters_def)
  show ?thesis
  proof (standard, goal_cases)
    case 1
    from char_one show ?case
      by (auto simp: lift_character_def simp del: char_one)
  next
    case (2 x)
    thus ?case by (auto simp: lift_character_def)
  next
    case (3 x y)
    from 3(1) obtain x' k where x: "x' \<in> H" "x = x' \<otimes> a (^) k" and k: "k < h"
      by (auto simp: adjoin_def h_def)
    from 3(2) obtain y' l where y: "y' \<in> H" "y = y' \<otimes> a (^) l" and l: "l < h"
      by (auto simp: adjoin_def h_def)
    have [simp]: "unadjoin x = (x', k)" using x k by (intro unadjoin_unique') (auto simp: h_def)
    have [simp]: "unadjoin y = (y', l)" using y l by (intro unadjoin_unique') (auto simp: h_def)
    have char_mult': "\<chi> (x \<otimes> y) = \<chi> x * \<chi> y" if "x \<in> H" "y \<in> H" for x y
      using char_mult[of x y] that by simp
    have char_power': "\<chi> (x (^) n) = \<chi> x ^ n" if "x \<in> H" for x n
      using that char_one by (induction n) (simp_all add: char_mult' del: char_one)

    define r where "r = (k + l) mod h"
    have r: "r < subgroup_indicator G H a" unfolding h_def r_def
      by (intro mod_less_divisor subgroup_indicator_pos is_subgroup) auto
    define zz where "zz = (a (^) h) (^) ((k + l) div h)"
    have [simp]: "zz \<in> H" unfolding zz_def h_def 
      by (rule nat_pow_closed) (auto intro: pow_subgroup_indicator is_subgroup)
    have "a (^) k \<otimes> a (^) l = zz \<otimes> a (^) r"
      by (simp add: nat_pow_mult zz_def nat_pow_pow r_def)
    with x y r have "unadjoin (x \<otimes> y) = (x' \<otimes> y' \<otimes> zz, r)"
      by (intro unadjoin_unique' m_closed) (auto simp: m_ac)
    hence "lift_character (\<chi>, z) (x \<otimes>\<^bsub>?G''\<^esub> y) = \<chi> (x' \<otimes> y' \<otimes> zz) * z ^ r"
      using 3 by (simp add: lift_character_def)
    also have "\<dots> = \<chi> x' * \<chi> y' * (\<chi> zz * z ^ r)"
      using x(1) y(1) by (simp add: char_mult' char_power')
    also have "\<chi> zz * z ^ r = z ^ (h * ((k + l) div h) + r)"
      unfolding h_def zz_def using \<open>subgroup H G\<close> assms(3)[symmetric] 
      by (subst char_power') (auto simp: pow_subgroup_indicator h_def power_mult power_add)
    also have "h * ((k + l) div h) + r = k + l" by (simp add: r_def)
    also have "\<chi> x' * \<chi> y' * z ^ (k + l) = lift_character (\<chi>,z) x * lift_character (\<chi>,z) y"
      using 3 by (simp add: lift_character_def power_add)
    finally show ?case .
  qed
qed

lemma lower_character_lift_character:
  assumes "\<chi> \<in> characters (G\<lparr>carrier := H\<rparr>)"
  shows   "(\<lambda>x. if x \<in> H then lift_character (\<chi>, z) x else 0) = \<chi>" (is ?th1)
          "lift_character (\<chi>, z) a = z" (is ?th2)
proof -
  from assms interpret \<chi>: character "G\<lparr>carrier := H\<rparr>" \<chi> by (simp add: characters_def)
  have char_mult: "\<chi> (x \<otimes> y) = \<chi> x * \<chi> y" if "x \<in> H" "y \<in> H" for x y
    using \<chi>.char_mult[of x y] that by simp
  have char_power: "\<chi> (x (^) n) = \<chi> x ^ n" if "x \<in> H" for x n
    using \<chi>.char_one that by (induction n) (simp_all add: char_mult)
  show ?th1 using \<chi>.char_eq_0 mem_adjoin[OF is_subgroup _ a_in_carrier]
    by (auto simp: lift_character_def)
  show ?th2 using \<chi>.char_one is_subgroup
    by (auto simp: lift_character_def adjoined_in_adjoin)
qed

lemma lift_character_lower_character:
  assumes "\<chi> \<in> characters (G\<lparr>carrier := adjoin G H a\<rparr>)"
  shows   "lift_character (\<lambda>x. if x \<in> H then \<chi> x else 0, \<chi> a) = \<chi>"
proof -
  let ?G' = "G\<lparr>carrier := adjoin G H a\<rparr>"
  from assms interpret \<chi>: character ?G' \<chi> by (simp add: characters_def)
  show ?thesis
  proof (rule ext, goal_cases)
    case (1 x)
    show ?case
    proof (cases "x \<in> adjoin G H a")
      case True
      note * = unadjoin_correct[OF this]
      interpret H': subgroup "adjoin G H a" G
        by (intro adjoin_subgroup is_subgroup a_in_carrier)
      have "x = fst (unadjoin x) \<otimes>\<^bsub>?G'\<^esub> a (^)\<^bsub>?G'\<^esub> snd (unadjoin x)" 
        using *(3) by (simp add: nat_pow_def)
      also have "\<chi> \<dots> = \<chi> (fst (unadjoin x)) * \<chi> (a (^)\<^bsub>?G'\<^esub> snd (unadjoin x))"
        using * is_subgroup by (intro \<chi>.char_mult) 
                               (auto simp: nat_pow_modify_carrier mem_adjoin adjoined_in_adjoin)
      also have "\<chi> (a (^)\<^bsub>?G'\<^esub> snd (unadjoin x)) = \<chi> a ^ snd (unadjoin x)"
        using is_subgroup by (intro \<chi>.char_power) (auto simp: adjoined_in_adjoin)
      finally show ?thesis using True * by (auto simp: lift_character_def)
    qed (auto simp: lift_character_def \<chi>.char_eq_0)
  qed
qed

lemma bij_betw_characters_adjoin:
  defines "h \<equiv> subgroup_indicator G H a"
  shows "bij_betw lift_character
                  (SIGMA \<chi>:characters (G\<lparr>carrier := H\<rparr>). {z. z ^ h = \<chi> (a (^) h)})
                  (characters (G\<lparr>carrier := adjoin G H a\<rparr>))"
proof (rule bij_betwI[where ?g = "\<lambda>\<chi>. (\<lambda>x. if x \<in> H then \<chi> x else 0, \<chi> a)"], goal_cases)
  case 1
  show ?case by (auto simp: characters_def h_def intro!: lift_character)
next
  case 2
  show ?case unfolding characters_def
  proof (safe, goal_cases)
    case (1 \<chi>)
    thus ?case unfolding h_def by (rule lower_character)
  next
    case (2 \<chi>)
    interpret \<chi>: character "G\<lparr>carrier := adjoin G H a\<rparr>" \<chi> by fact
    have [simp]: "\<chi> (a (^) n) = \<chi> a ^ n" for n using \<chi>.char_power[of a n] is_subgroup 
      by (auto simp: adjoined_in_adjoin nat_pow_def simp del: \<chi>.char_power)
    from is_subgroup a_in_carrier pow_subgroup_indicator show ?case
      by (auto simp: h_def intro!: subgroup_indicator_pos \<chi>.char_eq_0)
  qed
next
  case (3 w)
  thus ?case using lower_character_lift_character[of "fst w" "snd w"]
    by (auto cong: if_cong)
next
  case (4 \<chi>)
  thus ?case by (rule lift_character_lower_character)
qed

end


subsection \<open>Non-trivial facts about characters\<close>

context finite_comm_group
begin

text \<open>
  The number of characters is the same as the order of the group.

  We show this just like Apostol does by starting with the trivial group (which
  clearly has only the principal character) and then adjoining new elements until 
  we have reached $G$.

  Every time we adjoin an element $a\notin H$ to a subgroup $H$, each new character
  $\tilde{\chi}$ of $\langle H, a\rangle$ corresponds to a character $\chi$ of $H$
  and a $h$-th complex root of $\chi(a^h)$ (where $h$ is the indicator of 
  $\chi$ w.\,r.\,t.\ $H$), of which there are $h$. Since adjoining $a$ to $H$ also 
  increases the number of elements by a factor of $h$, the induction step is valid.
\<close>
theorem card_characters: "card (characters G) = order G"
proof (induction rule: subgroup_adjoin_induct')
  case singleton
  interpret G': group "G\<lparr>carrier := {\<one>}\<rparr>"
    by (intro subgroup_imp_group, standard) auto
  interpret G': finite_comm_group "G\<lparr>carrier := {\<one>}\<rparr>"
    by standard auto
  from singleton show ?case
    by (subst G'.characters_in_order_1) (simp_all add: order_def)
next
  case (adjoin H a)
  define h where "h = subgroup_indicator G H a"
  from adjoin have [simp]: "h > 0" unfolding h_def by (intro subgroup_indicator_pos) auto
  define c where "c = a (^) h"
  from adjoin have [simp]: "c \<in> H"
    by (auto simp: c_def h_def pow_subgroup_indicator)

  define roots :: "('a \<Rightarrow> complex) \<Rightarrow> complex set" where "roots = (\<lambda>\<chi>. {z. z ^ h = \<chi> c})"
  define G' G'' where "G' = G\<lparr>carrier := H\<rparr>" and "G'' = G\<lparr>carrier := adjoin G H a\<rparr>"
  interpret H: subgroup H G by fact
  have [simp,intro]: "finite H" using finite_subset[OF H.subset fin] .
  let ?h = "(\<lambda>\<chi>. (\<lambda>k. if k \<in> H then \<chi> k else 0, \<chi> a))"
  from adjoin have "order (G\<lparr>carrier := adjoin G H a\<rparr>) = card H * h"
    by (simp add: order_def card_adjoin h_def)
  interpret G': finite_comm_group G' unfolding G'_def by (rule subgroup_imp_finite_comm_group) fact
  interpret G'': finite_comm_group G'' unfolding G''_def 
    using adjoin by (intro subgroup_imp_finite_comm_group adjoin_subgroup) auto
  interpret adjoin: finite_comm_group_adjoin G H a
    by standard (insert adjoin.hyps, auto)

  have "card (characters G'') = card (SIGMA \<chi>:characters G'. roots \<chi>)"
    unfolding roots_def h_def G''_def G'_def c_def
    by (rule sym, rule bij_betw_same_card, rule adjoin.bij_betw_characters_adjoin)
  also have "\<dots> = (\<Sum>\<chi>\<in>characters G'. card (roots \<chi>))"
    by (intro card_SigmaI) (auto simp: roots_def)
  also have "\<dots> = (\<Sum>\<chi>\<in>characters G'. h)"
  proof (intro sum.cong refl, goal_cases)
    case (1 \<chi>)
    then interpret character G' \<chi> by (simp add: characters_def)
    have "\<chi> c \<noteq> 0"
      by (subst char_eq_0_iff) (auto simp: c_def G'_def h_def intro!: pow_subgroup_indicator adjoin)
    thus ?case by (simp add: roots_def card_nth_roots)
  qed
  also have "\<dots> = h * card (characters G')" by simp
  also have "card (characters G') = card H"
    by (simp add: G'_def adjoin.IH order_def)
  also have "h * card H = order (G\<lparr>carrier := adjoin G H a\<rparr>)"
    using adjoin by (simp add: order_def card_adjoin h_def)
  finally show ?case by (simp add: G''_def)
qed

end


text \<open>
  The entries of any non-principal character sum to 0.
\<close>
theorem (in character) sum_character:
  "(\<Sum>x\<in>carrier G. \<chi> x) = (if \<chi> = principal_char G then of_nat (order G) else 0)"
proof (cases "\<chi> = principal_char G")
  case True
  hence "(\<Sum>x\<in>carrier G. \<chi> x) = (\<Sum>x\<in>carrier G. 1)"
    by (intro sum.cong) (auto simp: principal_char_def)
  also have "\<dots> = order G" by (simp add: order_def)
  finally show ?thesis using True by simp
next
  case False
  define S where "S = (\<Sum>x\<in>carrier G. \<chi> x)"
  from False obtain y where y: "y \<in> carrier G" "\<chi> y \<noteq> 1"
    by (auto simp: principal_char_def fun_eq_iff char_eq_0_iff split: if_splits)
  from y have "S = (\<Sum>x\<in>carrier G. \<chi> (y \<otimes> x))" unfolding S_def
    by (intro sum.reindex_bij_betw [symmetric] bij_betw_mult_left)
  also have "\<dots> = (\<Sum>x\<in>carrier G. \<chi> y * \<chi> x)"
    by (intro sum.cong refl char_mult y)
  also have "\<dots> = \<chi> y * S" by (simp add: S_def sum_distrib_left)
  finally have "(\<chi> y - 1) * S = 0" by (simp add: algebra_simps)
  with y have "S = 0" by simp
  with False show ?thesis by (simp add: S_def)
qed

lemmas (in finite_comm_group) Characters_simps = 
  carrier_Characters mult_Characters one_Characters inv_Characters'

corollary (in finite_comm_group) character_orthogonality1:
  assumes "character G \<chi>" and "character G \<chi>'"
  shows   "(\<Sum>x\<in>carrier G. \<chi> x * cnj (\<chi>' x)) = (if \<chi> = \<chi>' then of_nat (order G) else 0)"
proof -
  define C where [simp]: "C = Characters G"
  interpret C: finite_comm_group C unfolding C_def
    by (rule finite_comm_group_Characters)
  let ?\<chi> = "\<lambda>x. \<chi> x * inv_character \<chi>' x"
  interpret character G "\<lambda>x. \<chi> x * inv_character \<chi>' x"
    by (intro character_mult character.inv_character assms)
  have "(\<Sum>x\<in>carrier G. \<chi> x * cnj (\<chi>' x)) = (\<Sum>x\<in>carrier G. ?\<chi> x)"
    by (intro sum.cong) (auto simp: inv_character_def)
  also have "\<dots> = (if ?\<chi> = principal_char G then of_nat (order G) else 0)"
    by (rule sum_character)
  also have "?\<chi> = principal_char G \<longleftrightarrow> \<chi> \<otimes>\<^bsub>C\<^esub> inv\<^bsub>C\<^esub> \<chi>' = \<one>\<^bsub>C\<^esub>"
    using assms by (simp add: Characters_simps characters_def)
  also have "\<dots> \<longleftrightarrow> \<chi> = \<chi>'"
  proof
    assume "\<chi> \<otimes>\<^bsub>C\<^esub> inv\<^bsub>C\<^esub> \<chi>' = \<one>\<^bsub>C\<^esub>"
    from C.inv_equality [OF this] and assms show "\<chi> = \<chi>'"
      by (auto simp: characters_def Characters_simps)
  next
    assume *: "\<chi> = \<chi>'"
    from assms show "\<chi> \<otimes>\<^bsub>C\<^esub> inv\<^bsub>C\<^esub> \<chi>' = \<one>\<^bsub>C\<^esub>" 
      by (subst *, intro C.r_inv) (auto simp: carrier_Characters characters_def)
  qed
  finally show ?thesis .
qed

context finite_comm_group
begin

text \<open>
  Summing the value of a fixed element for all characters yields the order of the
  group if that element is the neutral element of the group and 0 otherwise.

  Apostol shows this in a nice and elegant way using matrices: Representing every
  character as a row vector of its values, we get a square matrix $A$. The above 
  fact that the values of every non-principal character sum to 0 then implies 
  $A \cdot \frac{1}{n} A^* = I$ and therefore $\frac{1}{n} A^* \cdot A = 1$ since
  matrices commute with their inverses.

  Since matrices are a bit annoying to use in Isabelle at the moment, we shall 
  instead employ a more direct and arguably no less elegant method: We simply
  use a subgroup-adjoining induction similar to the one we used to show
  the previous result above the number of characters.

  We start with the group $\langle x \rangle$, i.\,e.\ @{term "adjoin G {\<one>} x"} 
  in Isabelle. Let $k$ be the order of $x$ in $G$. The characters of that subgroup 
  have a one-to-one correspondence to the $k$-th roots of unity, and summing all
  $k$-th roots of unity with $k > 1$ gives 0.

  On the other hand, when adjoining an element $a$ to a subgroup $H$ that already 
  contains $x$, the characters $\tilde{\chi}$ of $\langle H, a\rangle$ each arise 
  from a characters $\chi$ on $H$ and a $k'$-root of unity for some fixed $k'$, 
  where $\tilde{\chi}(x) = \chi(x)$, so that it is clear that the overall sum
  does not change at all.
\<close>
theorem sum_characters:
  assumes "x \<in> carrier G"
  shows   "(\<Sum>\<chi>\<in>characters G. \<chi> x) = (if x = \<one> then of_nat (order G) else 0)"
proof (cases "x = \<one>")
  case True
  hence "(\<Sum>\<chi>\<in>characters G. \<chi> x) = (\<Sum>\<chi>\<in>characters G. 1)"
    by (intro sum.cong refl) (auto intro!: character.char_one simp: characters_def)
  also have "\<dots> = order G" by (simp add: card_characters)
  finally show ?thesis using True by simp
next
  case False
  define H0 where "H0 = adjoin G {\<one>} x"
  have [simp]: "subgroup {\<one>} G" by standard auto
  with assms have "subgroup H0 G" unfolding H0_def by (intro adjoin_subgroup)
  hence "(\<Sum>\<chi>\<in>characters G. \<chi> x) = 0"
  proof (induction rule: subgroup_adjoin_induct)
    case base
    interpret finite_comm_group_adjoin G "{\<one>}" x
      by standard (use assms \<open>x \<noteq> \<one>\<close> in auto)
    interpret G': finite_comm_group "G\<lparr>carrier := {\<one>}\<rparr>" 
      by (rule subgroup_imp_finite_comm_group) fact
    from \<open>x \<noteq> \<one>\<close> have "ord x \<noteq> 1" using pow_ord_eq_1[OF fin assms] by (intro notI) auto
    with ord_pos[OF assms] have ord_x: "ord x > 1" by simp
    
    have "(\<Sum>\<chi>\<in>characters (G\<lparr>carrier := H0\<rparr>). \<chi> x) =
            (\<Sum>(\<chi>,z)\<in>(SIGMA \<chi>:{principal_char (G\<lparr>carrier := {\<one>}\<rparr>)}. 
               {z. z ^ ord x = \<chi> \<one>}). \<chi> (fst (unadjoin x)) * z ^ snd (unadjoin x))"
      unfolding H0_def using subgroup_indicator_trivial[OF assms] pow_ord_eq_1[OF fin assms]
      by (subst sum.reindex_bij_betw [OF bij_betw_characters_adjoin, symmetric])
         (simp_all add: characters_in_order_1 order_def G'.characters_in_order_1 
            lift_character_def case_prod_unfold adjoined_in_adjoin)
    also from ord_x have "\<dots> = \<Sum>{z. z ^ ord x = 1}"
      by (subst sum.Sigma [symmetric]) (simp_all add: principal_char_def finite_roots_unity)
    also have "\<dots> = 0" by (rule sum_roots_unity) fact
    finally show ?case .
  next
    case (adjoin H a)
    interpret H: subgroup H G by fact
    interpret finite_comm_group_adjoin G H a by standard (use adjoin in auto)
    interpret G': finite_comm_group "G\<lparr>carrier := H\<rparr>" 
      by (rule subgroup_imp_finite_comm_group) fact
    define h where "h = subgroup_indicator G H a"
    from adjoin have "h > 0" unfolding h_def by (intro subgroup_indicator_pos) auto
    from pow_subgroup_indicator[of H a] adjoin have "h \<noteq> 1" by (auto simp: h_def)
    with \<open>h > 0\<close> have "h > 1" by simp
    from assms have "x \<in> H0" by (auto simp: H0_def adjoined_in_adjoin)
    also note \<open>H0 \<subseteq> H\<close>
    finally have "x \<in> H" .

    have "(\<Sum>\<chi>\<in>characters (G\<lparr>carrier := adjoin G H a\<rparr>). \<chi> x) = 
             (\<Sum>(\<chi>,z)\<in>(SIGMA \<chi>:characters (G\<lparr>carrier := H\<rparr>). {z. z ^ h = \<chi> (a (^) h)}). \<chi> x)"
      using adjoin \<open>x \<in> H\<close>
      by (subst sum.reindex_bij_betw [OF bij_betw_characters_adjoin, symmetric])
         (simp_all add: lift_character_def case_prod_unfold mem_adjoin h_def [symmetric])
    also have "\<dots> = (\<Sum>\<chi>\<in>characters (G\<lparr>carrier := H\<rparr>). card {z. z ^ h = \<chi> (a (^) h)} * \<chi> x)"
      using \<open>h > 0\<close> by (subst sum.Sigma [symmetric]) auto
    also have "\<dots> = (\<Sum>\<chi>\<in>characters (G\<lparr>carrier := H\<rparr>). h * \<chi> x)"
    proof (intro sum.cong refl, goal_cases)
      case (1 \<chi>)
      then interpret character "G\<lparr>carrier := H\<rparr>" \<chi> by (simp add: characters_def)
      from adjoin have "\<chi> (a (^) h) \<noteq> 0" 
        by (subst char_eq_0_iff) (auto simp: h_def pow_subgroup_indicator)
      hence "card {z. z ^ h = \<chi> (a (^) h)} = h" using \<open>h > 1\<close>
        by (intro card_nth_roots) auto
      thus ?case by simp
    qed
    also have "\<dots> = 0"
      using adjoin by (simp add: sum_distrib_left [symmetric])
    finally show ?case .
  qed
  with False show ?thesis by simp
qed

corollary character_orthogonality2:
  assumes "x \<in> carrier G" "y \<in> carrier G"
  shows   "(\<Sum>\<chi>\<in>characters G. \<chi> x * cnj (\<chi> y)) = (if x = y then of_nat (order G) else 0)"
proof -
  from assms have "(\<Sum>\<chi>\<in>characters G. \<chi> x * cnj (\<chi> y)) = (\<Sum>\<chi>\<in>characters G. \<chi> (x \<otimes> inv y))"
    by (intro sum.cong) (simp_all add: character.char_inv character.char_mult characters_def)
  also from assms have "\<dots> = (if x \<otimes> inv y = \<one> then of_nat (order G) else 0)"
    by (intro sum_characters) auto
  also from assms have "x \<otimes> inv y = \<one> \<longleftrightarrow> x = y"
    using inv_equality[of x "inv y"] by auto
  finally show ?thesis .
qed

end

end
