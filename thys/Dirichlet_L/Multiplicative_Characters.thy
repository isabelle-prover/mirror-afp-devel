(*
    File:      Multiplicative_Characters.thy
    Author:    Manuel Eberl, TU München; Joseph Thommes, TU München
*)
section \<open>Multiplicative Characters of Finite Abelian Groups\<close>
theory Multiplicative_Characters
  imports
  Complex_Main
  "Finitely_Generated_Abelian_Groups.Finitely_Generated_Abelian_Groups"
begin

notation integer_mod_group ("Z")

subsection \<open>Definition of characters\<close>

text \<open>
  A (multiplicative) character is a completely multiplicative function from a group to the
  complex numbers. For simplicity, we restrict this to finite abelian groups here, which is
  the most interesting case.

  Characters form a group where the identity is the \emph{principal} character that maps all
  elements to $1$, multiplication is point-wise multiplication of the characters, and the inverse
  is the point-wise complex conjugate.

  This group is often called the \emph{Pontryagin dual} group and is isomorphic to the original
  group (in a non-natural way) while the double-dual group \<^emph>\<open>is\<close> naturally isomorphic to the
  original group.

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

lemma char_power [simp]: "a \<in> carrier G \<Longrightarrow> \<chi> (a [^] k) = \<chi> a ^ k"
  by (induction k) auto

lemma char_root:
  assumes "a \<in> carrier G"
  shows   "\<chi> a ^ ord a = 1"
proof -
  from assms have "\<chi> a ^ ord a = \<chi> (a [^] ord a)"
    by (subst char_power) auto
  also from fin and assms have "a [^] ord a = \<one>" by (intro pow_ord_eq_1) auto
  finally show ?thesis by simp
qed

lemma char_root':
  assumes "a \<in> carrier G"
  shows   "\<chi> a ^ order G = 1"
proof -
  from assms have "\<chi> a ^ order G = \<chi> (a [^] order G)" by simp
  also from fin and assms have "a [^] order G = \<one>" by (intro pow_order_eq_1) auto
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

lemma character_ext:
  assumes "character G \<chi>" "character G \<chi>'" "\<And>x. x \<in> carrier G \<Longrightarrow> \<chi> x = \<chi>' x"
  shows   "\<chi> = \<chi>'"
proof
  fix x :: 'a
  show "\<chi> x = \<chi>' x"
    using assms by (cases "x \<in> carrier G") (auto simp: character.char_eq_0)
qed

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


subsection \<open>The Character group\<close>

text \<open>
  The characters of a finite abelian group $G$ form another group $\widehat{G}$, which is called
  its Pontryagin dual group. This generalises to the more general setting of locally compact
  abelian groups, but we restrict ourselves to the finite setting because it is much easier.
\<close>
definition Characters :: "('a, 'b) monoid_scheme \<Rightarrow> ('a \<Rightarrow> complex) monoid"
  where "Characters G = \<lparr> carrier = characters G, monoid.mult = (\<lambda>\<chi>\<^sub>1 \<chi>\<^sub>2 k. \<chi>\<^sub>1 k * \<chi>\<^sub>2 k),
                          one = principal_char G \<rparr>"

lemma carrier_Characters: "carrier (Characters G) = characters G"
  by (simp add: Characters_def)

lemma one_Characters: "one (Characters G) = principal_char G"
  by (simp add: Characters_def)

lemma mult_Characters: "monoid.mult (Characters G) \<chi>\<^sub>1 \<chi>\<^sub>2 = (\<lambda>a. \<chi>\<^sub>1 a * \<chi>\<^sub>2 a)"
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

lemmas (in finite_comm_group) Characters_simps = 
  carrier_Characters mult_Characters one_Characters inv_Characters'

lemma inv_Characters': "\<chi> \<in> characters G \<Longrightarrow> inv\<^bsub>Characters G\<^esub> \<chi> = inv_character \<chi>"
  using character.inv_Characters[of G \<chi>] by (simp add: characters_def)

subsection \<open>The isomorphism between a group and its dual\<close>

text \<open>We start this section by inspecting the special case of a cyclic group. Here, any character
is fixed by the value it assigns to the generating element of the cyclic group. This can then be
used to construct a bijection between the nth unit roots and the elements of the character group -
implying the other results.\<close>

lemma (in finite_cyclic_group)
  defines ic: "induce_char \<equiv> (\<lambda>c::complex. (\<lambda>a. if a\<in>carrier G then c powi get_exp gen a else 0))"
  shows order_Characters: "order (Characters G) = order G"
  and   gen_fixes_char: "\<lbrakk>character G a; character G b; a gen = b gen\<rbrakk> \<Longrightarrow> a = b"
  and   unity_root_induce_char: "z ^ order G = 1 \<Longrightarrow> character G (induce_char z)"
proof -
  interpret C: finite_comm_group "Characters G" using finite_comm_group_Characters . 
  define n where "n = order G"
  hence n: "n > 0" using order_gt_0 by presburger
  from n_def have nog: "n = ord gen" using ord_gen_is_group_order by simp
  have xnz: "x \<noteq> 0" if "x ^ n = 1" for x::complex using n(1) that by (metis zero_neq_one zero_power)
  have m: "x powi m = x powi (m mod n)" if "x ^ n = 1" for x::complex and m::int
    using powi_mod[OF that n] .
  show cf: "character G (induce_char x)" if x: "x ^ n = 1" for x
  proof
    show "induce_char x \<one> \<noteq> 0" using xnz[OF that] unfolding ic by auto
    show "induce_char x a = 0" if "a \<notin> carrier G" for a using that unfolding ic by simp
    show "induce_char x (a \<otimes> b) = induce_char x a * induce_char x b"
      if "a \<in> carrier G" "b \<in> carrier G" for a b
    proof -
      have "x powi get_exp gen (a \<otimes> b) = x powi get_exp gen a * x powi get_exp gen b"
      proof -
        have "x powi get_exp gen (a \<otimes> b) = x powi ((get_exp gen a + get_exp gen b) mod n)"
          using m[OF x] get_exp_mult_mod[OF that] n_def ord_gen_is_group_order by metis
        also have "\<dots> = x powi (get_exp gen a + get_exp gen b)" using m[OF x] by presburger
        finally show ?thesis by (simp add: power_int_add xnz[OF x])
      qed
      thus ?thesis using that unfolding ic by simp
    qed
  qed
  define get_c where gc: "get_c = (\<lambda>c::'a \<Rightarrow> complex. c gen)"
  have biji: "bij_betw induce_char {z. z ^ n = 1} (characters G)"
   and bijg: "bij_betw get_c (characters G) {z. z ^ n = 1}"
  proof (intro bij_betwI[of _ _ _ get_c])
    show iin: "induce_char \<in> {z. z ^ n = 1} \<rightarrow> characters G" using cf unfolding characters_def
      by blast
    show gi: "get_c (induce_char x) = x" if "x \<in> {z. z ^ n = 1}" for x
    proof (cases "n = 1")
      case True
      with that have "x = 1" by force
      thus ?thesis unfolding ic gc by simp
    next
      case False
      have x: "x ^ n = 1" using that by blast
      have "x powi get_exp gen gen = x"
      proof -
        have "x powi get_exp gen gen = x powi (get_exp gen gen mod n)" using m[OF x] by blast
        moreover have "(get_exp gen gen mod n) = 1"
        proof -
          have "1 = 1 mod int n" using False n by auto
          also have "\<dots> = get_exp gen gen mod n"
            by (unfold nog, intro pow_eq_int_mod[OF gen_closed],
                use get_exp_fulfills[OF gen_closed] in auto)
          finally show ?thesis by argo
        qed
        ultimately show "x powi get_exp gen gen = x" by simp
      qed
      thus ?thesis unfolding ic gc by simp
    qed
    show gin: "get_c \<in> characters G \<rightarrow> {z. z ^ n = 1}"
    proof -
      have "False" if "get_c c ^ n \<noteq> 1" "character G c" for c
      proof -
        interpret character G c by fact
        show False using that(1)[unfolded gc] by (simp add: char_root' n_def)
      qed
      thus ?thesis unfolding characters_def by blast
    qed
    show ig: "induce_char (get_c y) = y" if y: "y \<in> characters G" for y
    proof (cases "n = 1")
      case True
      hence "y = principal_char G" using y n_def character.character_in_order_1 characters_def
        by auto
      thus ?thesis unfolding ic gc principal_char_def by force
    next
      case False
      have yc: "y \<in> carrier (Characters G)" using y[unfolded carrier_Characters[symmetric]] .
      interpret character G y using that unfolding characters_def by simp
      have ygo: "y gen ^ n = 1" using char_root'[OF gen_closed] n_def by blast
      have "y gen powi get_exp gen a = y a" if "a \<in> carrier G" for a using that
      proof(induction rule: generator_induct1)
        case gen
        have "y gen powi get_exp gen gen = y gen powi (get_exp gen gen mod n)"
          using m[OF ygo] by blast
        also have "\<dots> = y gen powi ((1::int) mod n)"
          using get_exp_self[OF gen_closed] nog by argo
        also have "\<dots> = y gen powi 1" using False n by simp
        finally have yg: "y gen powi get_exp gen gen = y gen" by simp
        thus ?case .
        case (step x)
        have "y gen powi get_exp gen (x \<otimes> gen) = y gen powi (get_exp gen (x \<otimes> gen) mod n)"
          using m[OF ygo] by blast
        also have "\<dots> = y gen powi ((get_exp gen x + get_exp gen gen) mod n)"
          using get_exp_mult_mod[OF step(1) gen_closed, unfolded nog[symmetric]] by argo
        also have "\<dots> = y gen powi (get_exp gen x + get_exp gen gen)" using m[OF ygo] by presburger
        also have "\<dots> = y gen powi get_exp gen x * y gen powi get_exp gen gen"
          by (simp add: char_eq_0_iff power_int_add)
        also have "\<dots> = y x * y gen" using yg step(2) by argo
        also have "\<dots> = y (x \<otimes> gen)" using step(1) by simp
        finally show ?case .
      qed
      thus "induce_char (get_c y) = y" unfolding ic gc using char_eq_0 by auto
    qed
    show "bij_betw get_c (characters G) {z. z ^ n = 1}" using ig gi iin gin
      by (auto intro: bij_betwI)
  qed
  with card_roots_unity_eq[OF n] n_def show "order (Characters G) = order G" unfolding order_def
    by (metis bij_betw_same_card carrier_Characters)
  assume assm: "character G a" "character G b" "a gen = b gen"
  with bijg[unfolded gc characters_def bij_betw_def inj_on_def] show "a = b" by auto
qed

text \<open>Moreover, we can show that a character that assigns a "true" root of unity to the
generating element of the group, generates the character group.\<close>

lemma (in finite_cyclic_group) finite_cyclic_group_Characters:
  obtains \<chi> where "finite_cyclic_group (Characters G) \<chi>"
proof -
  interpret C: finite_comm_group "Characters G" by (rule finite_comm_group_Characters)
  define n where n: "n = order G"
  hence nnz: "n \<noteq> 0" by blast
  from n have nog: "n = ord gen" using ord_gen_is_group_order by simp
  obtain x::complex where x: "x ^ n = 1" "\<And>m. \<lbrakk>0<m; m<n\<rbrakk> \<Longrightarrow> x ^ m \<noteq> 1"
    using true_nth_unity_root by blast
  have xnz: "x \<noteq> 0" using x n by (metis order_gt_0 zero_neq_one zero_power)
  have m: "x powi m = x powi (m mod n)" for m::int
    using powi_mod[OF x(1)] nnz by blast
  let ?f = "(\<lambda>a. if a \<in> carrier G then x powi (get_exp gen a) else 0)"
  have cf: "character G ?f" using unity_root_induce_char[OF x(1)[unfolded n]] .
  have fpow: "(?f [^]\<^bsub>Characters G\<^esub> m) a = x powi ((get_exp gen a) * m)"
    if "a \<in> carrier G" for a::'a and m::nat
    using that
  proof(unfold Characters_def principal_char_def, induction m)
    case s: (Suc m)
    have "x powi (get_exp gen a * int m) * x powi get_exp gen a
        = x powi (get_exp gen a * (1 + int m))"
    proof -
      fix ma :: nat
      have "x powi ((1 + int ma) * get_exp gen a)
          = x powi (get_exp gen a + int ma * get_exp gen a) \<and> 0 \<noteq> x"
        by (simp add: comm_semiring_class.distrib xnz)
      then show "x powi (get_exp gen a * int ma) * x powi get_exp gen a
               = x powi (get_exp gen a * (1 + int ma))"
        by (simp add: mult.commute power_int_add)
    qed
    thus ?case using s by simp
  qed simp
  interpret cyclic_group "Characters G" ?f
  proof (intro C.element_ord_generates_cyclic)
    show fc: "?f \<in> carrier (Characters G)" using cf carrier_Characters[of G] characters_def by fast
    from x nnz have fno: "?f [^]\<^bsub>Characters G\<^esub> m \<noteq> \<one>\<^bsub>Characters G\<^esub>" if "0 < m" "m < n" for m
    proof (cases "n = 1")
      case False
      have "\<one>\<^bsub>Characters G\<^esub> gen = 1" unfolding Characters_def principal_char_def using that by simp
      moreover have "(?f [^]\<^bsub>Characters G\<^esub> m) gen \<noteq> 1"
      proof -
        have "(?f [^]\<^bsub>Characters G\<^esub> m) gen = x powi ((get_exp gen gen) * m)" using fpow by blast
        also have "\<dots> = (x powi (get_exp gen gen)) ^ m" by (simp add: power_int_mult)
        also have "\<dots> = x ^ m"
        proof -
          have "x powi (get_exp gen gen) = x powi ((get_exp gen gen) mod n)" using m by blast
          moreover have "((get_exp gen gen) mod n) = 1"
          proof -
            have "1 = 1 mod int n" using False nnz by simp
            also have "\<dots> = get_exp gen gen mod n"
              by (unfold nog, intro pow_eq_int_mod[OF gen_closed],
                  use get_exp_fulfills[OF gen_closed] in auto)
            finally show ?thesis by argo
          qed
          ultimately have "x powi (get_exp gen gen) = x" by simp
          thus ?thesis by simp
        qed
        finally show ?thesis using x(2)[OF that] by argo
      qed
      ultimately show ?thesis by fastforce
    qed (use that in blast)
    have "C.ord ?f = n"
    proof -
      from nnz have "C.ord ?f \<le> n" unfolding n
        using C.ord_dvd_group_order[OF fc] order_Characters dvd_nat_bounds by auto
      with C.ord_conv_Least[OF fc] C.pow_order_eq_1[OF fc] n nnz show "C.ord ?f = n"
        by (metis (no_types, lifting) C.ord_pos C.pow_ord_eq_1 fc fno le_neq_implies_less)
    qed
    thus "C.ord ?f = order (Characters G)" using n order_Characters by argo
  qed
  have "finite_cyclic_group (Characters G) ?f" by unfold_locales
  with that show ?thesis by blast
qed

text \<open>And as two cyclic groups of the same order are isomorphic it follows the isomorphism of a
finite cyclic group and its dual.\<close>

lemma (in finite_cyclic_group) Characters_iso:
  "G \<cong> Characters G"
proof -
  from finite_cyclic_group_Characters obtain f where f: "finite_cyclic_group (Characters G) f" .
  then interpret C: finite_cyclic_group "Characters G" f .
  have "cyclic_group (Characters G) f" by unfold_locales
  from iso_cyclic_groups_same_order[OF this order_Characters[symmetric]] show ?thesis .
qed

text \<open>The character groups of two isomorphic groups are also isomorphic.\<close>

lemma (in finite_comm_group) iso_imp_iso_chars:
  assumes "G \<cong> H" "group H"
  shows "Characters G \<cong> Characters H"
proof -
  interpret H: finite_comm_group H by (rule iso_imp_finite_comm[OF assms])
  from assms have "H \<cong> G" using iso_sym by auto
  then obtain g where g: "g \<in> iso H G" unfolding is_iso_def by blast
  then interpret ggh: group_hom H G g by (unfold_locales, unfold iso_def, simp)
  let ?f = "(\<lambda>c a. if a \<in> carrier H then (c \<circ> g) a else 0)"
  have "?f \<in> iso (Characters G) (Characters H)"
  proof (intro isoI)
    interpret CG: finite_comm_group "Characters G" by (intro finite_comm_group_Characters)
    interpret CH: finite_comm_group "Characters H" by (intro H.finite_comm_group_Characters)
    have f_in: "?f x \<in> carrier (Characters H)" if "x \<in> carrier (Characters G)" for x
    proof (unfold carrier_Characters characters_def, rule, unfold_locales)
      interpret character G x using that characters_def carrier_Characters by blast
      show "(if \<one>\<^bsub>H\<^esub> \<in> carrier H then (x \<circ> g) \<one>\<^bsub>H\<^esub> else 0) \<noteq> 0" using g iso_iff by auto
      show "\<And>a. a \<notin> carrier H \<Longrightarrow> (if a \<in> carrier H then (x \<circ> g) a else 0) = 0" by simp
      show "?f x (a \<otimes>\<^bsub>H\<^esub> b) = ?f x a * ?f x b" if "a \<in> carrier H" "b \<in> carrier H" for a b
        using that by auto
    qed
    show "?f \<in> hom (Characters G) (Characters H)"
    proof (intro homI)
      show "?f x \<in> carrier (Characters H)" if "x \<in> carrier (Characters G)" for x
        using f_in[OF that] .
      show "?f (x \<otimes>\<^bsub>Characters G\<^esub> y) = ?f x \<otimes>\<^bsub>Characters H\<^esub> ?f y"
        if "x \<in> carrier (Characters G)" "y \<in> carrier (Characters G)" for x y
      proof -
        interpret x: character G x using that characters_def carrier_Characters by blast
        interpret y: character G y using that characters_def carrier_Characters by blast
        show ?thesis using that mult_Characters[of G] mult_Characters[of H] by auto
      qed
    qed
    show "bij_betw ?f (carrier (Characters G)) (carrier (Characters H))"
    proof(intro bij_betwI)
      define f where "f = inv_into (carrier H) g"
      hence f: "f \<in> iso G H" using H.iso_set_sym[OF g] by simp
      then interpret fgh: group_hom G H f by (unfold_locales, unfold iso_def, simp)
      let ?g = "(\<lambda>c a. if a \<in> carrier G then (c \<circ> f) a else 0)"
      show "?f \<in> carrier (Characters G) \<rightarrow> carrier (Characters H)" using f_in by fast
      show "?g \<in> carrier (Characters H) \<rightarrow> carrier (Characters G)"
      proof -
        have g_in: "?g x \<in> carrier (Characters G)" if "x \<in> carrier (Characters H)" for x
        proof (unfold carrier_Characters characters_def, rule, unfold_locales)
          interpret character H x using that characters_def carrier_Characters by blast
          show "(if \<one>\<^bsub>G\<^esub> \<in> carrier G then (x \<circ> f) \<one>\<^bsub>G\<^esub> else 0) \<noteq> 0" using f iso_iff by auto
          show "\<And>a. a \<notin> carrier G \<Longrightarrow> (if a \<in> carrier G then (x \<circ> f) a else 0) = 0" by simp
          show "?g x (a \<otimes>\<^bsub>G\<^esub> b) = ?g x a * ?g x b" if "a \<in> carrier G" "b \<in> carrier G" for a b
            using that by auto
        qed
        thus ?thesis by simp
      qed
      show "?f (?g x) = x" if x: "x \<in> carrier (Characters H)" for x
      proof -
        interpret character H x using x characters_def carrier_Characters by blast
        have "?f (?g x) a = x a" if a: "a \<notin> carrier H" for a using a char_eq_0[OF a] by auto
        moreover have "?f (?g x) a = x a" if a: "a \<in> carrier H" for a
        proof -
          from a have "inv_into (carrier H) g (g a) = a"
            by (simp add: g ggh.inj_iff_trivial_ker ggh.iso_kernel)
          thus ?thesis using a f_def by auto
        qed
        ultimately show ?thesis by fast
      qed
      show "?g (?f x) = x" if x: "x \<in> carrier (Characters G)" for x
      proof -
        interpret character G x using x characters_def carrier_Characters by blast
        have "?g (?f x) a = x a" if a: "a \<notin> carrier G" for a using a char_eq_0[OF a] by auto
        moreover have "?g (?f x) a = x a" if a: "a \<in> carrier G" for a using a f_def
        proof -
          from a have "g (inv_into (carrier H) g a) = a"
            by (meson f_inv_into_f g ggh.iso_iff subset_iff)
          thus ?thesis using a f_def fgh.hom_closed by auto
        qed
        ultimately show ?thesis by fast
      qed
    qed
  qed
  thus ?thesis unfolding is_iso_def by blast
qed

text \<open>The following two lemmas characterize the way a character behaves in a direct group product:
a character on the product induces characters on each of the factors. Also, any character on the
direct product can be decomposed into a pointwise product of characters on the factors.\<close>

lemma DirProds_subchar:
  assumes "finite_comm_group (DirProds Gs I)"
  and x: "x \<in> carrier (Characters (DirProds Gs I))" 
  and i: "i \<in> I"
  and I: "finite I"
  defines g: "g \<equiv> (\<lambda>c. (\<lambda>i\<in>I. (\<lambda>a. c ((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i:=a)))))"
  shows "character (Gs i) (g x i)"
proof -
  interpret DP: finite_comm_group "DirProds Gs I" by fact
  interpret xc: character "DirProds Gs I" x using x unfolding Characters_def characters_def by auto
  interpret Gi: finite_comm_group "Gs i"
    using i DirProds_finite_comm_group_iff[OF I] DP.finite_comm_group_axioms by blast
  have allg: "\<And>i. i\<in>I \<Longrightarrow> group (Gs i)" using DirProds_group_imp_groups[OF DP.is_group] .
  show ?thesis
  proof(unfold_locales)
    have "(\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>) = (\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := \<one>\<^bsub>Gs i\<^esub>)" using i by force
    thus "g x i \<one>\<^bsub>Gs i\<^esub> \<noteq> 0" using i g DirProds_one''[of Gs I] xc.char_one_nz by auto
    show "g x i a = 0" if a: "a \<notin> carrier (Gs i)" for a
    proof -
      from a i have "((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := a)) \<notin> carrier (DirProds Gs I)"
        unfolding DirProds_def by force
      from xc.char_eq_0[OF this] show ?thesis using i g by auto
    qed
    show "g x i (a \<otimes>\<^bsub>Gs i\<^esub> b) = g x i a * g x i b"
      if ab: "a \<in> carrier (Gs i)" "b \<in> carrier (Gs i)" for a b
    proof -
      have "g x i (a \<otimes>\<^bsub>Gs i\<^esub> b)
          = x ((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := a) \<otimes>\<^bsub>DirProds Gs I\<^esub> (\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := b))"
      proof -
        have "((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := a) \<otimes>\<^bsub>DirProds Gs I\<^esub> (\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := b))
            = ((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := (a \<otimes>\<^bsub>Gs i\<^esub> b)))"
        proof -
          have "((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := a) \<otimes>\<^bsub>DirProds Gs I\<^esub> (\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := b)) j
              = ((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := (a \<otimes>\<^bsub>Gs i\<^esub> b))) j"
            for j
          proof (cases "j \<in> I")
            case True
            from allg[OF True] interpret Gj: group "Gs j" .
            show ?thesis using ab True i unfolding DirProds_mult by simp
          next
            case False
            then show ?thesis unfolding DirProds_mult using i by fastforce
          qed
          thus ?thesis by fast
        qed
        thus ?thesis using i g by auto
      qed 
      also have "\<dots> = x ((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := a)) * x ((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := b))"
      proof -
        have ac: "((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := a)) \<in> carrier (DirProds Gs I)"
          unfolding DirProds_def using ab i monoid.one_closed[OF group.is_monoid[OF allg]] by force
        have bc: "((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := b)) \<in> carrier (DirProds Gs I)"
          unfolding DirProds_def using ab i monoid.one_closed[OF group.is_monoid[OF allg]] by force
        from xc.char_mult[OF ac bc] show ?thesis .
      qed
      also have "\<dots> = g x i a * g x i b" using i g by auto
      finally show ?thesis .
    qed
  qed
qed

lemma Characters_DirProds_single_prod:
  assumes "finite_comm_group (DirProds Gs I)"
  and x: "x \<in> carrier (Characters (DirProds Gs I))"
  and I: "finite I"
  defines g: "g \<equiv> (\<lambda>I. (\<lambda>c. (\<lambda>i\<in>I. (\<lambda>a. c ((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i:=a))))))"
  shows "(\<lambda>e. if e\<in>carrier(DirProds Gs I) then \<Prod>i\<in>I. (g I x i) (e i) else 0) = x" (is "?g x = x")
proof
  show "?g x e = x e" for e
  proof (cases "e \<in> carrier (DirProds Gs I)")
    case True
    show ?thesis using I x assms(1) True unfolding g
    proof(induction I arbitrary: x e rule: finite_induct)
      case empty
      interpret DP: finite_comm_group "DirProds Gs {}" by fact
      from DirProds_empty[of Gs] have "order (DirProds Gs {}) = 1" unfolding order_def by simp
      with DP.characters_in_order_1[OF this] empty(1) show ?case
        using DirProds_empty[of Gs] unfolding Characters_def principal_char_def by auto
    next
      case j: (insert j I)
      interpret DP: finite_comm_group "DirProds Gs (insert j I)" by fact
      interpret DP2: finite_comm_group "DirProds Gs I"
      proof -
        from DirProds_finite_comm_group_iff[of "insert j I" Gs] DP.finite_comm_group_axioms j
        have "(\<forall>i\<in>(insert j I). finite_comm_group (Gs i))" by blast
        with DirProds_finite_comm_group_iff[OF j(1), of Gs] show "finite_comm_group (DirProds Gs I)"
          by blast
      qed
      interpret xc: character "DirProds Gs (insert j I)" x
        using j(4) unfolding Characters_def characters_def by simp
      have allg: "\<And>i. i\<in>(insert j I) \<Longrightarrow> group (Gs i)"
        using DirProds_group_imp_groups[OF DP.is_group] .
      have e1c: "e(j:= \<one>\<^bsub>Gs j\<^esub>) \<in> carrier (DirProds Gs (insert j I))"
        using j(6) monoid.one_closed[OF group.is_monoid[OF allg[of j]]]
        unfolding DirProds_def PiE_def Pi_def by simp
      have e2c: "(\<lambda>i\<in>(insert j I). \<one>\<^bsub>Gs i\<^esub>)(j := e j) \<in> carrier (DirProds Gs (insert j I))"
        unfolding DirProds_def PiE_def Pi_def
        using monoid.one_closed[OF group.is_monoid[OF allg]] comp_in_carr[OF j(6)] by auto
      have "e = e(j:= \<one>\<^bsub>Gs j\<^esub>) \<otimes>\<^bsub>DirProds Gs (insert j I)\<^esub> (\<lambda>i\<in>(insert j I). \<one>\<^bsub>Gs i\<^esub>)(j := e j)"
      proof -
        have "e k
            = (e(j:= \<one>\<^bsub>Gs j\<^esub>) \<otimes>\<^bsub>DirProds Gs (insert j I)\<^esub> (\<lambda>i\<in>(insert j I). \<one>\<^bsub>Gs i\<^esub>)(j := e j)) k"
          for k
        proof(cases "k\<in>(insert j I)")
          case k: True
          from allg[OF k] interpret Gk: group "Gs k" .
          from allg[of j] interpret Gj: group "Gs j" by simp
          from k show ?thesis unfolding comp_mult[OF k] using comp_in_carr[OF j(6) k] by auto
        next
          case False
          then show ?thesis using j(6) unfolding DirProds_def by auto
        qed
        thus ?thesis by blast
      qed
      hence "x e = x (e(j:= \<one>\<^bsub>Gs j\<^esub>)) * x ((\<lambda>i\<in>(insert j I). \<one>\<^bsub>Gs i\<^esub>)(j := e j))"
        using xc.char_mult[OF e1c e2c] by argo
      also have "\<dots> = (\<Prod>i\<in>I. g (insert j I) x i (e i)) * g (insert j I) x j (e j)"
      proof -
        have "x (e(j:= \<one>\<^bsub>Gs j\<^esub>)) = (\<Prod>i\<in>I. g (insert j I) x i (e i))"
        proof -
          have eu: "e(j:=undefined) \<in> carrier (DirProds Gs I)" using j(2, 6)
            unfolding DirProds_def PiE_def Pi_def extensional_def by fastforce
          let ?x = "\<lambda>p. if p\<in>carrier(DirProds Gs I) then x (p(j:= \<one>\<^bsub>Gs j\<^esub>)) else 0"
          have cx2: "character (DirProds Gs I) ?x"
          proof
            show "?x \<one>\<^bsub>DirProds Gs I\<^esub> \<noteq> 0"
            proof -
              have "\<one>\<^bsub>DirProds Gs I\<^esub>(j := \<one>\<^bsub>Gs j\<^esub>) = \<one>\<^bsub>DirProds Gs (insert j I)\<^esub>"
                unfolding DirProds_one'' by force
              thus ?thesis by simp
            qed
            show "?x a = 0" if a: "a \<notin> carrier (DirProds Gs I)" for a using a by argo
            show "?x (a \<otimes>\<^bsub>DirProds Gs I\<^esub> b) = ?x a * ?x b"
              if ab: "a \<in> carrier (DirProds Gs I)" "b \<in> carrier (DirProds Gs I)" for a b
            proof -
              have ac: "a(j := \<one>\<^bsub>Gs j\<^esub>) \<in> carrier (DirProds Gs (insert j I))"
                using ab monoid.one_closed[OF group.is_monoid[OF allg[of j]]]
                unfolding DirProds_def PiE_def Pi_def by simp
              have bc: "b(j := \<one>\<^bsub>Gs j\<^esub>) \<in> carrier (DirProds Gs (insert j I))"
                using ab monoid.one_closed[OF group.is_monoid[OF allg[of j]]]
                unfolding DirProds_def PiE_def Pi_def by simp
              have m: "((a \<otimes>\<^bsub>DirProds Gs I\<^esub> b)(j := \<one>\<^bsub>Gs j\<^esub>))
                     = (a(j := \<one>\<^bsub>Gs j\<^esub>) \<otimes>\<^bsub>DirProds Gs (insert j I)\<^esub> b(j := \<one>\<^bsub>Gs j\<^esub>))"
              proof -
                have "((a \<otimes>\<^bsub>DirProds Gs I\<^esub> b)(j := \<one>\<^bsub>Gs j\<^esub>)) h
                    = (a(j := \<one>\<^bsub>Gs j\<^esub>) \<otimes>\<^bsub>DirProds Gs (insert j I)\<^esub> b(j := \<one>\<^bsub>Gs j\<^esub>)) h"
                  if h: "h\<in>(insert j I)" for h
                proof(cases "h=j")
                  case True
                  interpret Gj: group "Gs j" using allg[of j] by blast
                  from True comp_mult[OF h, of Gs "a(j := \<one>\<^bsub>Gs j\<^esub>)" "b(j := \<one>\<^bsub>Gs j\<^esub>)"] show ?thesis
                    by auto
                next
                  case False
                  interpret Gj: group "Gs h" using allg[OF h] .
                  from False h comp_mult[OF h, of Gs "a(j := \<one>\<^bsub>Gs j\<^esub>)" "b(j := \<one>\<^bsub>Gs j\<^esub>)"]
                       comp_mult[of h I Gs a b]
                  show ?thesis by auto
                qed
                moreover have "((a \<otimes>\<^bsub>DirProds Gs I\<^esub> b)(j := \<one>\<^bsub>Gs j\<^esub>)) h
                             = (a(j := \<one>\<^bsub>Gs j\<^esub>) \<otimes>\<^bsub>DirProds Gs (insert j I)\<^esub> b(j := \<one>\<^bsub>Gs j\<^esub>)) h"
                  if h: "h\<notin>(insert j I)" for h using h unfolding DirProds_def PiE_def by simp
                ultimately show ?thesis by blast
              qed
              have "x ((a \<otimes>\<^bsub>DirProds Gs I\<^esub> b)(j := \<one>\<^bsub>Gs j\<^esub>))
                  = x (a(j := \<one>\<^bsub>Gs j\<^esub>)) * x (b(j := \<one>\<^bsub>Gs j\<^esub>))"
                by (unfold m, intro xc.char_mult[OF ac bc])
              thus ?thesis using ab by auto
            qed
          qed
          then interpret cx2: character "DirProds Gs I" ?x .
          from cx2 have cx3:"?x \<in> carrier (Characters (DirProds Gs I))"
            unfolding Characters_def characters_def by simp
          from j(3)[OF cx3 DP2.finite_comm_group_axioms eu] have
           "(if e(j:=undefined) \<in> carrier (DirProds Gs I)
             then \<Prod>i\<in>I. g I ?x i ((e(j:=undefined)) i)
             else 0) = ?x (e(j:=undefined))"
            using eu j(2) unfolding g by fast
          with eu have "(\<Prod>i\<in>I. g I (\<lambda>p. if p \<in> carrier (DirProds Gs I)
                                         then x (p(j := \<one>\<^bsub>Gs j\<^esub>))
                                         else 0) i ((e(j := undefined)) i)) = x (e(j := \<one>\<^bsub>Gs j\<^esub>))"
            by simp
          moreover have "g I (\<lambda>a. if a \<in> carrier (DirProds Gs I)
                                  then x (a(j := \<one>\<^bsub>Gs j\<^esub>))
                                  else 0) i ((e(j := undefined)) i) = g (insert j I) x i (e i)"
            if i: "i\<in>I" for i
          proof -
            have "(\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := e i) \<in> carrier (DirProds Gs I)"
              unfolding DirProds_def PiE_def Pi_def extensional_def
              using monoid.one_closed[OF group.is_monoid[OF allg]] comp_in_carr[OF j(6)] i by simp
            moreover have "((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := e i, j := \<one>\<^bsub>Gs j\<^esub>))
                         = ((\<lambda>i\<in>insert j I. \<one>\<^bsub>Gs i\<^esub>)(i := e i))" using i j(2) by auto
            ultimately show ?thesis using i j(2, 4, 6) unfolding g by auto
          qed
          ultimately show ?thesis by simp
        qed
        moreover have "x ((\<lambda>i\<in>(insert j I). \<one>\<^bsub>Gs i\<^esub>)(j := e j)) = g (insert j I) x j (e j)"
          unfolding g by simp
        ultimately show ?thesis by argo
      qed  
      finally show ?case using j unfolding g by auto
    qed 
  next
    case False
    interpret xc: character "DirProds Gs I" x
      using x unfolding Characters_def characters_def by simp
    from xc.char_eq_0[OF False] False show ?thesis by argo
  qed
qed

text \<open>This allows for the following: the character group of a direct product is isomorphic to the
direct product of the character groups of the factors.\<close>

lemma (in finite_comm_group) Characters_DirProds_iso:
  assumes "DirProds Gs I \<cong> G" "group (DirProds Gs I)" "finite I"
  shows "DirProds (Characters \<circ> Gs) I \<cong> Characters G"
proof -
  interpret DP: group "DirProds Gs I" by fact
  interpret DP: finite_comm_group "DirProds Gs I"
    by (intro iso_imp_finite_comm[OF DP.iso_sym[OF assms(1)]], unfold_locales)
  interpret DPC: finite_comm_group "DirProds (Characters \<circ> Gs) I"
    using DirProds_finite_comm_group_iff[OF assms(3), of "Characters \<circ> Gs"]
          DirProds_finite_comm_group_iff[OF assms(3), of Gs]
          DP.finite_comm_group_axioms finite_comm_group.finite_comm_group_Characters by auto
  interpret CDP: finite_comm_group "Characters (DirProds Gs I)"
    using DP.finite_comm_group_Characters .
  interpret C: finite_comm_group "Characters G" using finite_comm_group_Characters .
  have allg: "\<And>i. i\<in>I \<Longrightarrow> group (Gs i)" using DirProds_group_imp_groups[OF assms(2)] .
  let ?f = "(\<lambda>cp. (\<lambda>e. (if e\<in>carrier (DirProds Gs I) then \<Prod>i\<in>I. cp i (e i) else 0)))"
  have f_in: "?f x \<in> carrier (Characters (DirProds Gs I))"
    if x: "x \<in> carrier (DirProds (Characters \<circ> Gs) I)" for x
  proof(unfold carrier_Characters characters_def, safe, unfold_locales)
    show "?f x \<one>\<^bsub>DirProds Gs I\<^esub> \<noteq> 0"
    proof -
      have "x i (\<one>\<^bsub>DirProds Gs I\<^esub> i) \<noteq> 0" if i: "i \<in> I" for i
      proof -
        interpret Gi: finite_comm_group "Gs i"
          using DirProds_finite_comm_group_iff[OF assms(3)] DP.finite_comm_group_axioms i by blast
        interpret xi: character "Gs i" "x i"
          using i x unfolding DirProds_def Characters_def characters_def by auto
        show ?thesis using DirProds_one'[OF i, of Gs] by simp
      qed
      thus ?thesis by (simp add: assms(3))
    qed
    show "?f x a = 0" if "a \<notin> carrier (DirProds Gs I)" for a using that by simp
    show "?f x (a \<otimes>\<^bsub>DirProds Gs I\<^esub> b) = ?f x a * ?f x b"
      if ab: "a \<in> carrier (DirProds Gs I)" "b \<in> carrier (DirProds Gs I)" for a b
    proof -
      have "a \<otimes>\<^bsub>DirProds Gs I\<^esub> b \<in> carrier (DirProds Gs I)" using that by blast
      moreover have "(\<Prod>i\<in>I. x i ((a \<otimes>\<^bsub>DirProds Gs I\<^esub> b) i))
                   = (\<Prod>i\<in>I. x i (a i)) * (\<Prod>i\<in>I. x i (b i))"
      proof -
        have "x i ((a \<otimes>\<^bsub>DirProds Gs I\<^esub> b) i) = x i (a i) * x i (b i)" if i: "i\<in>I" for i
        proof -
          interpret xi: character "Gs i" "x i"
            using i x unfolding DirProds_def Characters_def characters_def by auto
          show ?thesis using ab comp_mult[OF i, of Gs a b] by(auto simp: comp_in_carr[OF _ i])
        qed
        thus ?thesis using prod.distrib by force
      qed
      ultimately show ?thesis using that by auto
    qed
  qed
  have "?f \<in> iso (DirProds (Characters \<circ> Gs) I) (Characters (DirProds Gs I))"
  proof (intro isoI)
    show "?f \<in> hom (DirProds (Characters \<circ> Gs) I) (Characters (DirProds Gs I))"
    proof (intro homI)
      show "?f x \<in> carrier (Characters (DirProds Gs I))"
        if x: "x \<in> carrier (DirProds (Characters \<circ> Gs) I)" for x using f_in[OF that] .
      show "?f (x \<otimes>\<^bsub>DirProds (Characters \<circ> Gs) I\<^esub> y) = ?f x \<otimes>\<^bsub>Characters (DirProds Gs I)\<^esub> ?f y"
        if "x \<in> carrier (DirProds (Characters \<circ> Gs) I)" "y \<in> carrier (DirProds (Characters \<circ> Gs) I)"
        for x y
      proof -
        have "?f x \<otimes>\<^bsub>Characters (DirProds Gs I)\<^esub> ?f y
         = (\<lambda>e. if e \<in> carrier (DirProds Gs I) then (\<Prod>i\<in>I. x i (e i)) * (\<Prod>i\<in>I. y i (e i)) else 0)"
          unfolding Characters_def by auto
        also have "\<dots> = ?f (x \<otimes>\<^bsub>DirProds (Characters \<circ> Gs) I\<^esub> y)"
        proof -
          have "(\<Prod>i\<in>I. x i (e i)) * (\<Prod>i\<in>I. y i (e i))
              = (\<Prod>i\<in>I. (x \<otimes>\<^bsub>DirProds (Characters \<circ> Gs) I\<^esub> y) i (e i))" for e
            unfolding DirProds_def Characters_def by (auto simp: prod.distrib)
          thus ?thesis by presburger
        qed
        finally show ?thesis by argo
      qed
    qed
    then interpret fgh: group_hom "DirProds (Characters \<circ> Gs) I" "Characters (DirProds Gs I)" ?f
      by (unfold_locales, simp)
    show "bij_betw ?f (carrier (DirProds (Characters \<circ> Gs) I)) (carrier (Characters (DirProds Gs I)))"
    proof (intro bij_betwI)
      let ?g = "(\<lambda>c. (\<lambda>i\<in>I. (\<lambda>a. c ((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i:=a)))))"
      have allc: "character (Gs i) (?g x i)"
        if x: "x \<in> carrier (Characters (DirProds Gs I))" and i: "i \<in> I" for x i
        using DirProds_subchar[OF DP.finite_comm_group_axioms x i assms(3)] .
      have g_in: "?g x \<in> carrier (DirProds (Characters \<circ> Gs) I)"
        if x: "x \<in> carrier (Characters (DirProds Gs I))" for x
        using allc[OF x] unfolding DirProds_def Characters_def characters_def by simp
      show fi: "?f \<in> carrier (DirProds (Characters \<circ> Gs) I) \<rightarrow> carrier (Characters (DirProds Gs I))"
        using f_in by fast
      show gi: "?g \<in> carrier (Characters (DirProds Gs I)) \<rightarrow> carrier (DirProds (Characters \<circ> Gs) I)"
        using g_in by fast
      show "?f (?g x) = x" if x: "x \<in> carrier (Characters (DirProds Gs I))" for x
      proof -
        from x interpret x: character "DirProds Gs I" x unfolding Characters_def characters_def
          by auto
        from f_in[OF g_in[OF x]] interpret character "DirProds Gs I" "?f (?g x)"
          unfolding Characters_def characters_def by simp
        have "(\<Prod>i\<in>I. (\<lambda>i\<in>I. \<lambda>a. x ((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := a))) i (e i)) = x e"
          if e: "e \<in> carrier (DirProds Gs I)" for e
        proof -
          define y where y: "y = (\<lambda>e. if e \<in> carrier (DirProds Gs I)
                                      then \<Prod>i\<in>I. (\<lambda>i\<in>I. \<lambda>a. x ((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := a))) i (e i)
                                      else 0)"
          from Characters_DirProds_single_prod[OF DP.finite_comm_group_axioms x assms(3)]
          have "y = x" using y by force
          hence "y e = x e" by blast
          thus ?thesis using e unfolding y by argo
        qed
        with x.char_eq_0 show ?thesis by force
      qed
      show "?g (?f x) = x" if x: "x \<in> carrier (DirProds (Characters \<circ> Gs) I)" for x
      proof(intro eq_parts_imp_eq[OF g_in[OF f_in[OF x]] x])
        show "?g (?f x) i = x i" if i: "i\<in>I" for i
        proof -
          interpret xi: character "Gs i" "x i"
            using x i unfolding DirProds_def Characters_def characters_def by auto 
          have "?g (?f x) i a = x i a" if a: "a\<notin>carrier (Gs i)" for a
          proof -
            have "(\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := a) \<notin> carrier (DirProds Gs I)"
              using a i unfolding DirProds_def PiE_def Pi_def by auto
            with xi.char_eq_0[OF a] a i show ?thesis by auto
          qed
          moreover have "?g (?f x) i a = x i a" if a: "a\<in>carrier (Gs i)" for a
          proof -
            have "(\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := a) \<in> carrier (DirProds Gs I)"
              using a i monoid.one_closed[OF group.is_monoid[OF allg]]
              unfolding DirProds_def by force
            moreover have "(\<Prod>j\<in>I. x j (((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := a)) j)) = x i a"
            proof -
              have "(\<Prod>j\<in>I. x j (((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := a)) j))
               = x i (((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := a)) i) * (\<Prod>j\<in>I-{i}. x j (((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := a)) j))"
                by (meson assms(3) i prod.remove)
              moreover have "x j (((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := a)) j) = 1" if j: "j\<in>I" "j \<noteq> i" for j
              proof -
                interpret xj: character "Gs j" "x j"
                  using j(1) x unfolding DirProds_def Characters_def characters_def by auto
                show ?thesis using j by auto
              qed
              moreover have "x i (((\<lambda>i\<in>I. \<one>\<^bsub>Gs i\<^esub>)(i := a)) i) = x i a" by simp
              ultimately show ?thesis by auto
            qed
            ultimately show ?thesis using a i by simp
          qed
          ultimately show ?thesis by blast
        qed
      qed
    qed
  qed
  hence "DirProds (Characters \<circ> Gs) I \<cong> Characters (DirProds Gs I)" unfolding is_iso_def by blast
  moreover have "Characters (DirProds Gs I) \<cong> Characters G"
    using DP.iso_imp_iso_chars[OF assms(1) is_group] .
  ultimately show ?thesis using iso_trans by blast
qed

text \<open>As thus both the group and its character group can be decomposed into the same cyclic factors,
the isomorphism follows for any finite abelian group.\<close>

theorem (in finite_comm_group) Characters_iso:
  shows "G \<cong> Characters G"
proof -
  from cyclic_product obtain ns
    where ns: "DirProds (\<lambda>n. Z (ns ! n)) {..<length ns} \<cong> G" "\<forall>n\<in>set ns. n \<noteq> 0" .
  interpret DP: group "DirProds (\<lambda>n. Z (ns ! n)) {..<length ns}"
    by (intro DirProds_is_group, auto)
  have "G \<cong> DirProds (\<lambda>n. Z (ns ! n)) {..<length ns}" using DP.iso_sym[OF ns(1)] .
  moreover have "DirProds (Characters \<circ> (\<lambda>n. Z (ns ! n))) {..<length ns} \<cong> Characters G"
    by (intro Characters_DirProds_iso[OF ns(1) DirProds_is_group], auto)
  moreover have "DirProds (\<lambda>n. Z (ns ! n)) {..<length ns}
               \<cong> DirProds (Characters \<circ> (\<lambda>n. Z (ns ! n))) {..<length ns}"
  proof (intro DirProds_iso1)
    fix i assume i: "i \<in> {..<length ns}"
    obtain a where "cyclic_group (Z (ns!i)) a" using Zn_cyclic_group .
    then interpret Zi: cyclic_group "Z (ns!i)" a .
    interpret Zi: finite_cyclic_group "Z (ns!i)" a
    proof
      have "order (Z (ns ! i)) \<noteq> 0" using ns(2) i Zn_order by simp
      thus "finite (carrier (Z (ns ! i)))" unfolding order_def by (simp add: card_eq_0_iff)
    qed
    show "Group.group ((Characters \<circ> (\<lambda>n. Z (ns ! n))) i)"
         "Group.group (Z (ns ! i))" "Z (ns ! i) \<cong> (Characters \<circ> (\<lambda>n. Z (ns ! n))) i"
      using Zi.Characters_iso Zi.finite_comm_group_Characters comm_group_def finite_comm_group_def
      by auto
  qed
  ultimately show ?thesis by (auto elim: iso_trans)
qed

text \<open>Hence, the orders are also equal.\<close>

corollary (in finite_comm_group) order_Characters:
  "order (Characters G) = order G"
  using iso_same_card[OF Characters_iso] unfolding order_def by argo

corollary (in finite_comm_group) card_characters: "card (characters G) = order G"
  using order_Characters unfolding order_def Characters_def by simp

subsection \<open>Non-trivial facts about characters\<close>

text \<open>We characterize the character group of a quotient group as the group of characters that map
all elements of the subgroup onto $1$.\<close>

lemma (in finite_comm_group) iso_Characters_FactGroup:
  assumes H: "subgroup H G"
  shows "(\<lambda>\<chi> x. if x \<in> carrier G then \<chi> (H #> x) else 0) \<in>
           iso (Characters (G Mod H)) ((Characters G)\<lparr>carrier := {\<chi>\<in>characters G. \<forall>x\<in>H. \<chi> x = 1}\<rparr>)"
proof -
  interpret H: normal H G using subgroup_imp_normal[OF H] .
  interpret Chars: finite_comm_group "Characters G"
    by (rule finite_comm_group_Characters)
  interpret Fact: comm_group "G Mod H"
    by (simp add: H.subgroup_axioms comm_group.abelian_FactGroup comm_group_axioms)
  interpret Fact: finite_comm_group "G Mod H"
    by unfold_locales (auto simp: carrier_FactGroup)

  define C :: "('a \<Rightarrow> complex) set" where "C = {\<chi>\<in>characters G. \<forall>x\<in>H. \<chi> x = 1}"
  interpret C: subgroup C "Characters G"
  proof (unfold_locales, goal_cases)
    case 1
    thus ?case
      by (auto simp: C_def one_Characters mult_Characters carrier_Characters characters_def)
  next
    case 2
    thus ?case
      by (auto simp: C_def one_Characters mult_Characters carrier_Characters characters_def)
  next
    case 3
    thus ?case
      by (auto simp: C_def one_Characters mult_Characters
                     carrier_Characters characters_def principal_char_def)
  next
    case (4 \<chi>)
    hence "inv\<^bsub>Characters G\<^esub> \<chi> = inv_character \<chi>"
      by (subst inv_Characters') (auto simp: C_def carrier_Characters)
    moreover have "inv_character \<chi> \<in> characters G"
      using 4 by (auto simp: C_def characters_def)
    moreover have "\<forall>x\<in>H. inv_character \<chi> x = 1"
      using 4 by (auto simp: C_def inv_character_def)
    ultimately show ?case
      by (auto simp: C_def)
  qed

  define f :: "('a set \<Rightarrow> complex) \<Rightarrow> ('a \<Rightarrow> complex)"
    where "f = (\<lambda>\<chi> x. if x \<in> carrier G then \<chi> (H #> x) else 0)"

  have [intro]: "character G (f \<chi>)" if "character (G Mod H) \<chi>" for \<chi>
  proof -
    interpret character "G Mod H" \<chi> by fact
    show ?thesis
    proof (unfold_locales, goal_cases)
      case 1
      thus ?case by (auto simp: f_def char_eq_0_iff carrier_FactGroup)
    next
      case (2 x)
      thus ?case by (auto simp: f_def)
    next
      case (3 x y)
      have "\<chi> (H #> x) * \<chi> (H #> y) = \<chi> ((H #> x) \<otimes>\<^bsub>G Mod H\<^esub> (H #> y))"
        using 3 by (intro char_mult [symmetric]) (auto simp: carrier_FactGroup)
      also have "(H #> x) \<otimes>\<^bsub>G Mod H\<^esub> (H #> y) = H #> (x \<otimes> y)"
        using 3 by (simp add: H.rcos_sum)
      finally show ?case
        using 3 by (simp add: f_def)
    qed
  qed

  have [intro]: "f \<chi> \<in> C" if "character (G Mod H) \<chi>" for \<chi>
  proof -
    interpret \<chi>: character "G Mod H" \<chi>
      by fact
    have "character G (f \<chi>)"
      using \<chi>.character_axioms by auto
    moreover have "\<chi> (H #> x) = 1" if "x \<in> H" for x
      using that H.rcos_const \<chi>.char_one by force
    ultimately show ?thesis
      by (auto simp: carrier_Characters C_def characters_def f_def)
  qed

  show "f \<in> iso (Characters (G Mod H)) ((Characters G)\<lparr>carrier := C\<rparr>)"
  proof (rule isoI)
    show "f \<in> hom (Characters (G Mod H)) (Characters G\<lparr>carrier := C\<rparr>)"
    proof (rule homI, goal_cases)
      case (1 \<chi>)
      thus ?case
        by (auto simp: carrier_Characters characters_def)
    qed (auto simp: f_def carrier_Characters fun_eq_iff mult_Characters)
  next
    have "bij_betw f (characters (G Mod H)) C"
      unfolding bij_betw_def
    proof
      show inj: "inj_on f (characters (G Mod H))"
      proof (rule inj_onI, goal_cases)
        case (1 \<chi>1 \<chi>2)
        interpret \<chi>1: character "G Mod H" \<chi>1
          using 1 by (auto simp: characters_def)
        interpret \<chi>2: character "G Mod H" \<chi>2
          using 1 by (auto simp: characters_def)

        have "\<chi>1 H' = \<chi>2 H'" for H'
        proof (cases "H' \<in> carrier (G Mod H)")
          case False
          thus ?thesis by (simp add: \<chi>1.char_eq_0 \<chi>2.char_eq_0)
        next
          case True
          then obtain x where x: "x \<in> carrier G" "H' = H #> x"
            by (auto simp: carrier_FactGroup)
          from 1 have "f \<chi>1 x = f \<chi>2 x"
            by simp
          with x show ?thesis
            by (auto simp: f_def)
        qed
        thus "\<chi>1 = \<chi>2" by force
      qed
    
      have "f ` characters (G Mod H) \<subseteq> C"
        by (auto simp: characters_def)
      moreover have "C \<subseteq> f ` characters (G Mod H)"
      proof safe
        fix \<chi> assume \<chi>: "\<chi> \<in> C"
        from \<chi> interpret character G \<chi>
          by (auto simp: C_def characters_def)
        have [simp]: "\<chi> x = 1" if "x \<in> H" for x
          using \<chi> that by (auto simp: C_def)

        have "\<forall>H'\<in>carrier (G Mod H). \<exists>x\<in>carrier G. H' = H #> x"
          by (auto simp: carrier_FactGroup)
        then obtain h where h: "h H' \<in> carrier G" "H' = H #> h H'" if "H' \<in> carrier (G Mod H)" for H'
          by metis
        define \<chi>' where "\<chi>' = (\<lambda>H'. if H' \<in> carrier (G Mod H) then \<chi> (h H') else 0)"

        have \<chi>_cong: "\<chi> x = \<chi> y" if "H #> x = H #> y" "x \<in> carrier G" "y \<in> carrier G" for x y
        proof -
          have "x \<in> H #> x"
            by (simp add: H.subgroup_axioms rcos_self that(2))
          also have "\<dots> = H #> y"
            by fact
          finally obtain z where z: "z \<in> H" "x = z \<otimes> y"
            unfolding r_coset_def by auto
          thus ?thesis
            using z H.subset that by simp
        qed

        have "character (G Mod H) \<chi>'"
        proof (unfold_locales, goal_cases)
          case 1
          have H: "H \<in> carrier (G Mod H)"
            using Fact.one_closed unfolding one_FactGroup .
          with h[of H] have "h H \<in> carrier G"
            by blast
          thus ?case using H
            by (auto simp: char_eq_0_iff \<chi>'_def)
        next
          case (2 H')
          thus ?case by (auto simp: \<chi>'_def)
        next
          case (3 H1 H2)
          from 3 have H12: "H1 <#> H2 \<in> carrier (G Mod H)"
            using Fact.m_closed by force
          have "\<chi> (h (H1 <#> H2)) = \<chi> (h H1 \<otimes> h H2)"
          proof (rule \<chi>_cong)
            show "H #> h (H1 <#> H2) = H #> (h H1 \<otimes> h H2)"
              by (metis "3" H.rcos_sum H12 h)
          qed (use 3 h[of H1] h[of H2] h[OF H12] in auto)
          thus ?case
            using 3 H12 h[of H1] h[of H2] by (auto simp: \<chi>'_def)
        qed

        moreover have "f \<chi>' x = \<chi> x" for x
        proof (cases "x \<in> carrier G")
          case False
          thus ?thesis
            by (auto simp: f_def \<chi>'_def char_eq_0_iff)
        next
          case True
          hence *: "H #> x \<in> carrier (G Mod H)"
            by (auto simp: carrier_FactGroup)
          have "\<chi> (h (H #> x)) = \<chi> x"
            using True * h[of "H #> x"] by (intro \<chi>_cong) auto
          thus ?thesis
            using True * by (auto simp: f_def fun_eq_iff \<chi>'_def)
        qed
        hence "f \<chi>' = \<chi>" by force

        ultimately show "\<chi> \<in> f ` characters (G Mod H)"
          unfolding characters_def by blast
      qed

      ultimately show "f ` characters (G Mod H) = C"
        by blast

    qed
    thus "bij_betw f (carrier (Characters (G Mod H))) (carrier (Characters G\<lparr>carrier := C\<rparr>))"
      by (simp add: carrier_Characters)
  qed 
qed

lemma (in finite_comm_group) is_iso_Characters_FactGroup:
  assumes H: "subgroup H G"
  shows "Characters (G Mod H) \<cong> (Characters G)\<lparr>carrier := {\<chi>\<in>characters G. \<forall>x\<in>H. \<chi> x = 1}\<rparr>"
  using iso_Characters_FactGroup[OF assms] unfolding is_iso_def by blast

text \<open>In order to derive the number of extensions a character on a subgroup has to the entire group,
we introduce the group homomorphism \<open>restrict_char\<close> that restricts a character to a given subgroup \<open>H\<close>.\<close>

definition restrict_char::"'a set \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> ('a \<Rightarrow> complex) " where
"restrict_char H \<chi> = (\<lambda>e. if e\<in>H then \<chi> e else 0)"

lemma (in finite_comm_group) restrict_char_hom:
  assumes "subgroup H G"
  shows "group_hom (Characters G) (Characters (G\<lparr>carrier := H\<rparr>)) (restrict_char H)"
proof -
  let ?CG = "Characters G"
  let ?H = "G\<lparr>carrier := H\<rparr>"
  let ?CH = "Characters ?H" 
  interpret H: subgroup H G by fact
  interpret H: finite_comm_group ?H by (simp add: assms subgroup_imp_finite_comm_group)
  interpret CG: finite_comm_group ?CG using finite_comm_group_Characters .
  interpret CH: finite_comm_group ?CH using H.finite_comm_group_Characters .
  show ?thesis
  proof(unfold_locales, intro homI)
    show "restrict_char H x \<in> carrier ?CH" if x: "x \<in> carrier ?CG" for x
    proof -
      interpret xc: character G x using x unfolding Characters_def characters_def by simp
      have "character ?H (restrict_char H x)"
        by (unfold restrict_char_def, unfold_locales, auto)
      thus ?thesis unfolding Characters_def characters_def by simp
    qed
    show "restrict_char H (x \<otimes>\<^bsub>?CG\<^esub> y) = restrict_char H x \<otimes>\<^bsub>?CH\<^esub> restrict_char H y"
      if x: "x \<in> carrier ?CG" and y: "y \<in> carrier ?CG" for x y
    proof -
      interpret xc: character G x using x unfolding Characters_def characters_def by simp
      interpret yc: character G y using y unfolding Characters_def characters_def by simp
      show ?thesis unfolding Characters_def restrict_char_def by auto
    qed
  qed
qed

text \<open>The kernel is just the set of the characters that are $1$ on all of \<open>H\<close>.\<close>

lemma (in finite_comm_group) restrict_char_kernel:
  assumes "subgroup H G"
  shows "kernel (Characters G) (Characters (G\<lparr>carrier := H\<rparr>)) (restrict_char H)
       = {\<chi>\<in>characters G. \<forall>x\<in>H. \<chi> x = 1}"
  by (unfold restrict_char_def kernel_def one_Characters
             carrier_Characters principal_char_def characters_def, simp, metis)

text \<open>Also, all of the characters on the subgroup are the image of some character on the whole group.\<close>

lemma (in finite_comm_group) restrict_char_image:
  assumes "subgroup H G"
  shows "restrict_char H ` (carrier (Characters G)) = carrier (Characters (G\<lparr>carrier := H\<rparr>))"
proof -
  interpret H: subgroup H G by fact
  interpret H: finite_comm_group "G\<lparr>carrier := H\<rparr>" using subgroup_imp_finite_comm_group[OF assms] .
  interpret r: group_hom "Characters G" "Characters (G\<lparr>carrier := H\<rparr>)" "restrict_char H"
    using restrict_char_hom[OF assms] .
  interpret Mod: finite_comm_group "G Mod H" using finite_comm_FactGroup[OF assms] .
  interpret CG: finite_comm_group "Characters G" using finite_comm_group_Characters .
  have c1: "order (Characters (G\<lparr>carrier := H\<rparr>)) = card H" using H.order_Characters
    unfolding order_def by simp
  
  have "card H * card (kernel (Characters G) (Characters (G\<lparr>carrier := H\<rparr>)) (restrict_char H))
      = order G"
    using restrict_char_kernel[OF assms] iso_same_card[OF is_iso_Characters_FactGroup[OF assms]]
          Mod.order_Characters lagrange[OF assms] unfolding order_def FactGroup_def
    by (force simp: algebra_simps)
  moreover have "card (kernel (Characters G) (Characters (G\<lparr>carrier := H\<rparr>)) (restrict_char H)) \<noteq> 0"
    using r.one_in_kernel unfolding kernel_def CG.fin by auto
  ultimately have c2: "card H = card (restrict_char H ` carrier (Characters G))"
    using r.image_kernel_product[unfolded order_Characters] by (metis mult_right_cancel)

  have "restrict_char H ` (carrier (Characters G)) \<subseteq> carrier (Characters (G\<lparr>carrier := H\<rparr>))"
    by auto
  with c2 H.fin show ?thesis
    by (auto, metis H.finite_imp_card_positive c1 card_subset_eq fin_gen
                    order_def r.H.order_gt_0_iff_finite)
qed

text \<open>
  It follows that any character on \<open>H\<close> can be extended
  to a character on \<open>G\<close>.
\<close>

lemma (in finite_comm_group) character_extension_exists:
  assumes "subgroup H G" "character (G\<lparr>carrier := H\<rparr>) \<chi>"
  obtains \<chi>' where "character G \<chi>'" and "\<And>x. x \<in> H \<Longrightarrow> \<chi>' x = \<chi> x"
proof -
  from restrict_char_image[OF assms(1)] assms(2) obtain \<chi>'
    where chi': "restrict_char H \<chi>' = \<chi>" "character G \<chi>'"
    by (force simp: carrier_Characters characters_def)
  thus ?thesis using that restrict_char_def by metis
qed

text \<open>For two characters on a group \<open>G\<close> the number of characters on subgroup \<open>H\<close> that share the
values with them is the same for both.\<close>

lemma (in finite_comm_group) character_restrict_card: 
  assumes "subgroup H G" "character G a" "character G b"
  shows   "card {\<chi>'\<in>characters G. \<forall>x\<in>H. \<chi>' x = a x} = card {\<chi>'\<in>characters G. \<forall>x\<in>H. \<chi>' x = b x}"
proof -
  interpret H: subgroup H G by fact
  interpret H: finite_comm_group "G\<lparr>carrier := H\<rparr>" using assms(1)
    by (simp add: subgroup_imp_finite_comm_group)
  interpret CG: finite_comm_group "Characters G" using finite_comm_group_Characters .
  interpret a: character G a by fact
  interpret b: character G b by fact
  have ac: "a \<in> carrier (Characters G)" unfolding Characters_def characters_def using assms by simp
  have bc: "b \<in> carrier (Characters G)" unfolding Characters_def characters_def using assms by simp
  define f where f: "f = (\<lambda>c. b \<otimes>\<^bsub>Characters G\<^esub> inv\<^bsub>Characters G\<^esub> a \<otimes>\<^bsub>Characters G\<^esub> c)"
  define g where g: "g = (\<lambda>c. a \<otimes>\<^bsub>Characters G\<^esub> inv\<^bsub>Characters G\<^esub> b \<otimes>\<^bsub>Characters G\<^esub> c)"
  let ?A = "{\<chi>'\<in>characters G. \<forall>x\<in>H. \<chi>' x = a x}"
  let ?B = "{\<chi>'\<in>characters G. \<forall>x\<in>H. \<chi>' x = b x}"
  have "bij_betw f ?A ?B"
  proof(intro bij_betwI[of _ _ _ g])
    show "f \<in> ?A \<rightarrow> ?B"
    proof
      show "f x \<in> ?B" if x: "x \<in> ?A" for x
      proof -
        interpret xc: character G x using x unfolding characters_def by blast
        have xc: "x \<in> carrier (Characters G)" using x unfolding Characters_def by simp
        have "f x y = b y" if y: "y \<in> H" for y
        proof -
          have "(inv\<^bsub>Characters G\<^esub> a) y * a y =  1"
            by (simp add: a.inv_Characters a.mult_inv_character mult.commute principal_char_def y)
          thus ?thesis unfolding f mult_Characters using x y by fastforce
        qed
        thus "f x \<in> ?B" unfolding f carrier_Characters[symmetric] using ac bc xc by blast
      qed
    qed
    show "g \<in> ?B \<rightarrow> ?A"
    proof
      show "g x \<in> ?A" if x: "x \<in> ?B" for x
      proof -
        interpret xc: character G x using x unfolding characters_def by blast
        have xc: "x \<in> carrier (Characters G)" using x unfolding Characters_def by simp
        have "g x y = a y" if y: "y \<in> H" for y
        proof -
          have "(inv\<^bsub>Characters G\<^esub> b) y * x y = 1" using x y
            by (simp add: b.inv_Characters b.mult_inv_character mult.commute principal_char_def)
          thus ?thesis unfolding g mult_Characters by simp
        qed
        thus "g x \<in> ?A" unfolding g carrier_Characters[symmetric] using ac bc xc by blast
      qed
    qed
    show "g (f x) = x" if x: "x \<in> ?A" for x
    proof -
      have xc: "x \<in> carrier (Characters G)" using x unfolding Characters_def by force
      with ac bc show ?thesis unfolding f g
        by (auto simp: CG.m_assoc[symmetric],
            metis CG.inv_closed CG.inv_comm CG.l_inv CG.m_assoc CG.r_one)
    qed
    show "f (g x) = x" if x: "x \<in> ?B" for x
    proof -
      have xc: "x \<in> carrier (Characters G)" using x unfolding Characters_def by force
      with ac bc show ?thesis unfolding f g
        by (auto simp: CG.m_assoc[symmetric],
            metis CG.inv_closed CG.inv_comm CG.l_inv CG.m_assoc CG.r_one)
    qed
  qed
  thus ?thesis using bij_betw_same_card by blast
qed

text \<open>These lemmas allow to show that the number of extensions of a character on \<open>H\<close> to a
character on \<open>G\<close> is just $|G|/|H|$.\<close>

theorem (in finite_comm_group) card_character_extensions:
  assumes "subgroup H G" "character (G\<lparr>carrier := H\<rparr>) \<chi>"
  shows   "card {\<chi>'\<in>characters G. \<forall>x\<in>H. \<chi>' x = \<chi> x} * card H = order G"
proof -
  interpret H: subgroup H G by fact
  interpret H: finite_comm_group "G\<lparr>carrier := H\<rparr>"
    using subgroup_imp_finite_comm_group[OF assms(1)] .
  interpret chi: character "G\<lparr>carrier := H\<rparr>" \<chi> by fact
  interpret C: finite_comm_group "Characters G" using finite_comm_group_Characters .
  interpret Mod: finite_comm_group "G Mod H" using finite_comm_FactGroup[OF assms(1)] .
  obtain a where a: "a \<in> carrier (Characters G)" "restrict_char H a = \<chi>"
  proof -
    have "\<exists>a\<in>carrier (Characters G). restrict_char H a = \<chi>"
      using restrict_char_image[OF assms(1)] assms(2)
      unfolding carrier_Characters characters_def image_def by force
    thus ?thesis using that by blast
  qed
  show ?thesis
  proof -
    have p: "{\<chi>\<in>characters G. \<forall>x\<in>H. \<chi> x = 1} = {\<chi>\<in>characters G. \<forall>x\<in>H. \<chi> x = principal_char G x}"
      unfolding principal_char_def by force
    have ac: "{\<chi>'\<in>characters G. \<forall>x\<in>H. \<chi>' x = \<chi> x} = {\<chi>'\<in>characters G. \<forall>x\<in>H. \<chi>' x = a x}"
      using a(2) unfolding restrict_char_def by force
    have "card {\<chi>\<in>characters G. \<forall>x\<in>H. \<chi> x = 1} = card {\<chi>'\<in>characters G. \<forall>x\<in>H. \<chi>' x = \<chi> x}"
      by (unfold ac p; intro character_restrict_card[OF assms(1)],
          use a[unfolded Characters_def characters_def] in auto)
    moreover have "card {\<chi>\<in>characters G. \<forall>x\<in>H. \<chi> x = 1} = card (carrier (G Mod H))"
      using iso_same_card[OF is_iso_Characters_FactGroup[OF assms(1)]]
            Mod.order_Characters[unfolded order_def] by force
    moreover have "card (carrier (G Mod H)) * card H = order G"
      using lagrange[OF assms(1)] unfolding FactGroup_def by simp
    ultimately show ?thesis by argo
  qed
qed

text \<open>
  Lastly, we can also show that for each $x\in H$ of order $n > 1$ and each \<open>n\<close>-th root of
  unity \<open>z\<close>, there exists a character \<open>\<chi>\<close> on \<open>G\<close> such that $\chi(x) = z$.
\<close>

lemma (in group) powi_get_exp_self:
  fixes z::complex
  assumes "z ^ n = 1" "x \<in> carrier G" "ord x = n" "n > 1"
  shows "z powi get_exp x x = z"
proof -
  from assms have ngt0: "n > 0" by simp
  from powi_mod[OF assms(1) ngt0, of "get_exp x x"] get_exp_self[OF assms(2), unfolded assms(3)]
  have "z powi get_exp x x = z powi (1 mod int n)" by argo    
  also have "\<dots> = z" using assms(4) by simp
  finally show ?thesis .
qed

corollary (in finite_comm_group) character_with_value_exists:
  assumes "x \<in> carrier G" and "x \<noteq> \<one>" and "z ^ ord x = 1"
  obtains \<chi> where "character G \<chi>" and "\<chi> x = z"
proof -
  interpret H: subgroup "generate G {x}" G using generate_is_subgroup assms(1) by simp
  interpret H: finite_comm_group "G\<lparr>carrier := generate G {x}\<rparr>"
    using subgroup_imp_finite_comm_group[OF H.subgroup_axioms] . 
  interpret H: finite_cyclic_group "G\<lparr>carrier := generate G {x}\<rparr>" x
  proof(unfold finite_cyclic_group_def, safe)
    show "finite_group (G\<lparr>carrier := generate G {x}\<rparr>)" by unfold_locales
    show "cyclic_group (G\<lparr>carrier := generate G {x}\<rparr>) x"
    proof(intro H.cyclic_groupI0)
      show "x \<in> carrier (G\<lparr>carrier := generate G {x}\<rparr>)" using generate.incl[of x "{x}" G] by simp
      show "carrier (G\<lparr>carrier := generate G {x}\<rparr>) = generate (G\<lparr>carrier := generate G {x}\<rparr>) {x}"
        using generate_consistent[OF generate_sincl H.subgroup_axioms] by simp
    qed
  qed
  have ox: "H.ord x = ord x" using H.gen_closed H.subgroup_axioms subgroup_ord_eq by auto
  have ogt1: "ord x > 1" using ord_pos by (metis assms(1, 2) less_one nat_neq_iff ord_eq_1)
  from assms H.unity_root_induce_char[unfolded H.ord_gen_is_group_order[symmetric] ox, OF assms(3)]
  obtain c where c: "character (G\<lparr>carrier := generate G {x}\<rparr>) c"
                    "c = (\<lambda>a. if a \<in> carrier (G\<lparr>carrier := generate G {x}\<rparr>)
                              then z powi H.get_exp x a else 0)" by blast
  have cx: "c x = z" unfolding c(2)
    using H.powi_get_exp_self[OF assms(3) _ ox ogt1] generate_sincl[of "{x}"] by simp
  obtain f where f: "character G f" "\<And>y. y \<in> (generate G {x}) \<Longrightarrow> f y = c y"
    using character_extension_exists[OF H.subgroup_axioms c(1)] by blast
  show ?thesis by (intro that[OF f(1)], use cx f(2) generate_sincl in blast)
qed

text \<open>
  In particular, for any \<open>x\<close> that is not the identity element, there exists a character \<open>\<chi>\<close>
  such that $\chi(x)\neq 1$.
\<close>
corollary (in finite_comm_group) character_neq_1_exists:
  assumes "x \<in> carrier G" and "x \<noteq> \<one>"
  obtains \<chi> where "character G \<chi>" and "\<chi> x \<noteq> 1"
proof -
  define z where "z = cis (2 * pi / ord x)"
  have z_pow_h: "z ^ ord x = 1"
    by (auto simp: z_def DeMoivre)

  from assms have "ord x \<ge> 1" by (intro ord_ge_1) auto
  moreover have "ord x \<noteq> 1"
    using pow_ord_eq_1[of x] assms fin by (intro notI) simp_all
  ultimately have "ord x > 1" by linarith

  have [simp]: "z \<noteq> 1"
  proof
    assume "z = 1"
    have "bij_betw (\<lambda>k. cis (2 * pi * real k / real (ord x))) {..<ord x} {z. z ^ ord x = 1}"
      using \<open>ord x > 1\<close> by (intro bij_betw_roots_unity) auto
    hence inj: "inj_on (\<lambda>k. cis (2 * pi * real k / real (ord x))) {..<ord x}"
      by (auto simp: bij_betw_def)
    have "0 = (1 :: nat)"
      using \<open>z = 1\<close> and \<open>ord x > 1\<close> by (intro inj_onD[OF inj]) (auto simp: z_def)
    thus False by simp
  qed

  obtain \<chi> where "character G \<chi>" and "\<chi> x = z"
    using character_with_value_exists[OF assms z_pow_h] .
  thus ?thesis using that[of \<chi>] by simp
qed

subsection \<open>The first orthogonality relation\<close>

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


subsection \<open>The isomorphism between a group and its double dual\<close>

text \<open>
  Lastly, we show that the double dual of a finite abelian group is naturally isomorphic
  to the original group via the obvious isomorphism $x\mapsto (\chi\mapsto \chi(x))$.
  It is easy to see that this is a homomorphism and that it is injective. The fact 
  $|\widehat{\widehat{G}}| = |\widehat{G}| = |G|$ then shows that it is also surjective.
\<close>
context finite_comm_group
begin

definition double_dual_iso :: "'a \<Rightarrow> ('a \<Rightarrow> complex) \<Rightarrow> complex" where
  "double_dual_iso x = (\<lambda>\<chi>. if character G \<chi> then \<chi> x else 0)"

lemma double_dual_iso_apply [simp]: "character G \<chi> \<Longrightarrow> double_dual_iso x \<chi> = \<chi> x"
  by (simp add: double_dual_iso_def)

lemma character_double_dual_iso [intro]:
  assumes x: "x \<in> carrier G"
  shows   "character (Characters G) (double_dual_iso x)"
proof -
  interpret G': finite_comm_group "Characters G"
    by (rule finite_comm_group_Characters)
  show "character (Characters G) (double_dual_iso x)"
    using x by unfold_locales (auto simp: double_dual_iso_def characters_def Characters_def
                                              principal_char_def character.char_eq_0)
qed

lemma double_dual_iso_mult [simp]:
  assumes "x \<in> carrier G" "y \<in> carrier G"
  shows   "double_dual_iso (x \<otimes> y) =
             double_dual_iso x \<otimes>\<^bsub>Characters (Characters G)\<^esub> double_dual_iso y"
  using assms by (auto simp: double_dual_iso_def Characters_def fun_eq_iff character.char_mult)

lemma double_dual_iso_one [simp]:
  "double_dual_iso \<one> = principal_char (Characters G)"
  by (auto simp: fun_eq_iff double_dual_iso_def principal_char_def
                 carrier_Characters characters_def character.char_one)

lemma inj_double_dual_iso: "inj_on double_dual_iso (carrier G)"
proof -
  interpret G': finite_comm_group "Characters G"
    by (rule finite_comm_group_Characters)
  interpret G'': finite_comm_group "Characters (Characters G)"
    by (rule G'.finite_comm_group_Characters)
  have hom: "double_dual_iso \<in> hom G (Characters (Characters G))"
    by (rule homI) (auto simp: carrier_Characters characters_def)
  have inj_aux: "x = \<one>"
    if x: "x \<in> carrier G" "double_dual_iso x = \<one>\<^bsub>Characters (Characters G)\<^esub>" for x
  proof (rule ccontr)
    assume "x \<noteq> \<one>"
    obtain \<chi> where \<chi>: "character G \<chi>" "\<chi> x \<noteq> 1"
      using character_neq_1_exists[OF x(1) \<open>x \<noteq> \<one>\<close>] .
    from x have "\<forall>\<chi>. (if \<chi> \<in> characters G then \<chi> x else 0) = (if \<chi> \<in> characters G then 1 else 0)"
      by (auto simp: double_dual_iso_def Characters_def fun_eq_iff
                     principal_char_def characters_def)
    hence eq1: "\<forall>\<chi>\<in>characters G. \<chi> x = 1" by metis
    with \<chi> show False unfolding characters_def by auto
  qed
  thus ?thesis
    using inj_aux hom is_group G''.is_group by (subst inj_on_one_iff') auto
qed

lemma double_dual_iso_eq_iff [simp]:
  "x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> double_dual_iso x = double_dual_iso y \<longleftrightarrow> x = y"
  by (auto dest: inj_onD[OF inj_double_dual_iso])

theorem double_dual_iso: "double_dual_iso \<in> iso G (Characters (Characters G))"
proof (rule isoI)
  interpret G': finite_comm_group "Characters G"
    by (rule finite_comm_group_Characters)
  interpret G'': finite_comm_group "Characters (Characters G)"
    by (rule G'.finite_comm_group_Characters)

  show hom: "double_dual_iso \<in> hom G (Characters (Characters G))"
    by (rule homI) (auto simp: carrier_Characters characters_def)

  show "bij_betw double_dual_iso (carrier G) (carrier (Characters (Characters G)))"
    unfolding bij_betw_def
  proof
    show "inj_on double_dual_iso (carrier G)" by (fact inj_double_dual_iso)
  next
    show "double_dual_iso ` carrier G = carrier (Characters (Characters G))"
    proof (rule card_subset_eq)
      show "finite (carrier (Characters (Characters G)))"
        by (fact G''.fin)
    next
      have "card (carrier (Characters (Characters G))) = card (carrier G)"
        by (simp add: carrier_Characters G'.card_characters card_characters order_def)
      also have "\<dots> = card (double_dual_iso ` carrier G)"
        by (intro card_image [symmetric] inj_double_dual_iso)
      finally show "card (double_dual_iso ` carrier G) =
                      card (carrier (Characters (Characters G)))" ..
    next
      show "double_dual_iso ` carrier G \<subseteq> carrier (Characters (Characters G))"
        using hom by (auto simp: hom_def)
    qed
  qed
qed

lemma double_dual_is_iso: "Characters (Characters G) \<cong> G"
  by (rule iso_sym) (use double_dual_iso in \<open>auto simp: is_iso_def\<close>)

text \<open>
  The second orthogonality relation follows from the first one via Pontryagin duality:
\<close>
theorem sum_characters:
  assumes x: "x \<in> carrier G"
  shows   "(\<Sum>\<chi>\<in>characters G. \<chi> x) = (if x = \<one> then of_nat (order G) else 0)"
proof -
  interpret G': finite_comm_group "Characters G"
    by (rule finite_comm_group_Characters)
  interpret x: character "Characters G" "double_dual_iso x"
    using x by auto
  from x.sum_character show ?thesis using double_dual_iso_eq_iff[of x \<one>] x
    by (auto simp: characters_def carrier_Characters order_Characters simp del: double_dual_iso_eq_iff)
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

no_notation integer_mod_group ("Z")
end
