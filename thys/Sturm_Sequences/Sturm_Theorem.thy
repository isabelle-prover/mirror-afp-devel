section {* Proof of Sturm's Theorem *}
(* Author: Manuel Eberl <eberlm@in.tum.de> *)
theory Sturm_Theorem
imports "~~/src/HOL/Library/Poly_Deriv" "Lib/Sturm_Library"
begin

subsection {* Sign changes of polynomial sequences *}

text {*
  For a given sequence of polynomials, this function computes the number of sign changes
  of the sequence of polynomials evaluated at a given position $x$. A sign change is a
  change from a negative value to a positive one or vice versa; zeros in the sequence are
  ignored.
*}

definition sign_changes where
"sign_changes ps (x::real) =
    length (remdups_adj (filter (\<lambda>x. x \<noteq> 0) (map (\<lambda>p. sgn (poly p x)) ps))) - 1"

text {*
  The number of sign changes of a sequence distributes over a list in the sense that
  the number of sign changes of a sequence $p_1, \ldots, p_i, \ldots, p_n$ at $x$ is the same
  as the sum of the sign changes of the sequence $p_1, \ldots, p_i$ and $p_i, \ldots, p_n$
  as long as $p_i(x)\neq 0$.
*}

lemma sign_changes_distrib:
  "poly p x \<noteq> 0 \<Longrightarrow>
      sign_changes (ps\<^sub>1 @ [p] @ ps\<^sub>2) x =
      sign_changes (ps\<^sub>1 @ [p]) x + sign_changes ([p] @ ps\<^sub>2) x"
  by (simp add: sign_changes_def sgn_zero_iff, subst remdups_adj_append, simp)

text {*
  The following two congruences state that the number of sign changes is the same
  if all the involved signs are the same.
*}

lemma sign_changes_cong:
  assumes "length ps = length ps'"
  assumes "\<forall>i < length ps. sgn (poly (ps!i) x) = sgn (poly (ps'!i) y)"
  shows "sign_changes ps x = sign_changes ps' y"
proof-
 from assms(2) have A: "map (\<lambda>p. sgn (poly p x)) ps = map (\<lambda>p. sgn (poly p y)) ps'"
  proof (induction rule: list_induct2[OF assms(1)])
    case 1
      then show ?case by simp
  next
    case (2 p ps p' ps')
      from 2(3)
      have "\<forall>i<length ps. sgn (poly (ps ! i) x) =
                         sgn (poly (ps' ! i) y)" by auto
      from 2(2)[OF this] 2(3) show ?case by auto
  qed
  show ?thesis unfolding sign_changes_def by (simp add: A)
qed

lemma sign_changes_cong':
  assumes "\<forall>p \<in> set ps. sgn (poly p x) = sgn (poly p y)"
  shows "sign_changes ps x = sign_changes ps y"
using assms by (intro sign_changes_cong, simp_all)

text {*
  For a sequence of polynomials of length 3, if the first and the third
  polynomial have opposite and nonzero sign at some $x$, the number of
  sign changes is always 1, irrespective of the sign of the second
  polynomial.
*}

lemma sign_changes_sturm_triple:
  assumes "poly p x \<noteq> 0" and "sgn (poly r x) = - sgn (poly p x)"
  shows "sign_changes [p,q,r] x = 1"
unfolding sign_changes_def by (insert assms, auto simp: sgn_real_def)

text {*
  Finally, we define two additional functions that count the sign changes ``at infinity''.
*}

definition sign_changes_inf where
"sign_changes_inf ps =
    length (remdups_adj (filter (\<lambda>x. x \<noteq> 0) (map poly_inf ps))) - 1"

definition sign_changes_neg_inf where
"sign_changes_neg_inf ps =
    length (remdups_adj (filter (\<lambda>x. x \<noteq> 0) (map poly_neg_inf ps))) - 1"



subsection {* Definition of Sturm sequences locale *}

text {*
  We first define the notion of a ``Quasi-Sturm sequence'', which is a weakening of
  a Sturm sequence that captures the properties that are fulfilled by a nonempty
  suffix of a Sturm sequence:
  \begin{itemize}
    \item The sequence is nonempty.
    \item The last polynomial does not change its sign.
    \item If the middle one of three adjacent polynomials has a root at $x$, the other
          two have opposite and nonzero signs at $x$.
  \end{itemize}
*}

locale quasi_sturm_seq =
  fixes ps :: "(real poly) list"
  assumes last_ps_sgn_const[simp]:
      "\<And>x y. sgn (poly (last ps) x) = sgn (poly (last ps) y)"
  assumes ps_not_Nil[simp]: "ps \<noteq> []"
  assumes signs: "\<And>i x. \<lbrakk>i < length ps - 2; poly (ps ! (i+1)) x = 0\<rbrakk>
                     \<Longrightarrow> (poly (ps ! (i+2)) x) * (poly (ps ! i) x) < 0"


text {*
  Now we define a Sturm sequence $p_1,\ldots,p_n$ of a polynomial $p$ in the following way:
  \begin{itemize}
    \item The sequence contains at least two elements.
    \item $p$ is the first polynomial, i.\,e. $p_1 = p$.
    \item At any root $x$ of $p$, $p_2$ and $p$ have opposite sign left of $x$ and
          the same sign right of $x$ in some neighbourhood around $x$.
    \item The first two polynomials in the sequence have no common roots.
    \item If the middle one of three adjacent polynomials has a root at $x$, the other
          two have opposite and nonzero signs at $x$.
  \end{itemize}
*}

locale sturm_seq = quasi_sturm_seq +
  fixes p :: "real poly"
  assumes hd_ps_p[simp]: "hd ps = p"
  assumes length_ps_ge_2[simp]: "length ps \<ge> 2"
  assumes deriv: "\<And>x\<^sub>0. poly p x\<^sub>0 = 0 \<Longrightarrow>
      eventually (\<lambda>x. sgn (poly (p * ps!1) x) =
                      (if x > x\<^sub>0 then 1 else -1)) (at x\<^sub>0)"
  assumes p_squarefree: "\<And>x. \<not>(poly p x = 0 \<and> poly (ps!1) x = 0)"
begin

  text {*
    Any Sturm sequence is obviously a Quasi-Sturm sequence.
  *}
  lemma quasi_sturm_seq: "quasi_sturm_seq ps" ..

(*<*)
  lemma ps_first_two:
    obtains q ps' where "ps = p # q # ps'"
    using hd_ps_p length_ps_ge_2
      by (cases ps, simp, clarsimp, rename_tac ps', case_tac ps', auto)

  lemma ps_first: "ps ! 0 = p" by (rule ps_first_two, simp)

  lemma [simp]: "p \<in> set ps" using hd_in_set[OF ps_not_Nil] by simp
(*>*)
end

(*<*)
lemma [simp]: "\<not>quasi_sturm_seq []" by (simp add: quasi_sturm_seq_def)
(*>*)

text {*
  Any suffix of a Quasi-Sturm sequence is again a Quasi-Sturm sequence.
*}

lemma quasi_sturm_seq_Cons:
  assumes "quasi_sturm_seq (p#ps)" and "ps \<noteq> []"
  shows "quasi_sturm_seq ps"
proof (unfold_locales)
  show "ps \<noteq> []" by fact
next
  from assms(1) interpret quasi_sturm_seq "p#ps" .
  fix x y
  from last_ps_sgn_const and `ps \<noteq> []`
      show "sgn (poly (last ps) x) = sgn (poly (last ps) y)" by simp_all
next
  from assms(1) interpret quasi_sturm_seq "p#ps" .
  fix i x
  assume "i < length ps - 2" and "poly (ps ! (i+1)) x = 0"
  with signs[of "i+1"]
      show "poly (ps ! (i+2)) x * poly (ps ! i) x < 0" by simp
qed



subsection {* Auxiliary lemmas about roots and sign changes *}

lemma sturm_adjacent_root_aux:
  assumes "i < length (ps :: real poly list) - 1"
  assumes "poly (ps ! i) x = 0" and "poly (ps ! (i + 1)) x = 0"
  assumes "\<And>i x. \<lbrakk>i < length ps - 2; poly (ps ! (i+1)) x = 0\<rbrakk>
                   \<Longrightarrow> sgn (poly (ps ! (i+2)) x) = - sgn (poly (ps ! i) x)"
  shows "\<forall>j\<le>i+1. poly (ps ! j) x = 0"
using assms
proof (induction i)
  case 0 thus ?case by (clarsimp, rename_tac j, case_tac j, simp_all)
next
  case (Suc i)
    from Suc.prems(1,2)
        have "sgn (poly (ps ! (i + 2)) x) = - sgn (poly (ps ! i) x)"
        by (intro assms(4)) simp_all
    with Suc.prems(3) have "poly (ps ! i) x = 0" by (simp add: sgn_zero_iff)
    with Suc.prems have "\<forall>j\<le>i+1. poly (ps ! j) x = 0"
        by (intro Suc.IH, simp_all)
    with Suc.prems(3) show ?case
      by (clarsimp, rename_tac j, case_tac "j = Suc (Suc i)", simp_all)
qed


text {*
  This function splits the sign list of a Sturm sequence at a
  position @{term x} that is not a root of @{term p} into a
  list of sublists such that the number of sign changes within
  every sublist is constant in the neighbourhood of @{term x},
  thus proving that the total number is also constant.
*}
fun split_sign_changes where
"split_sign_changes [p] (x :: real) = [[p]]" |
"split_sign_changes [p,q] x = [[p,q]]" |
"split_sign_changes (p#q#r#ps) x =
    (if poly p x \<noteq> 0 \<and> poly q x = 0 then
       [p,q,r] # split_sign_changes (r#ps) x
     else
       [p,q] # split_sign_changes (q#r#ps) x)"

lemma (in quasi_sturm_seq) split_sign_changes_subset[dest]:
  "ps' \<in> set (split_sign_changes ps x) \<Longrightarrow> set ps' \<subseteq> set ps"
apply (insert ps_not_Nil)
apply (induction ps x rule: split_sign_changes.induct)
apply (simp, simp, rename_tac p q r ps x,
       case_tac "poly p x \<noteq> 0 \<and> poly q x = 0", auto)
done

text {*
  A custom induction rule for @{term split_sign_changes} that
  uses the fact that all the intermediate parameters in calls
  of @{term split_sign_changes} are quasi-Sturm sequences.
*}
lemma (in quasi_sturm_seq) split_sign_changes_induct:
  "\<lbrakk>\<And>p x. P [p] x; \<And>p q x. quasi_sturm_seq [p,q] \<Longrightarrow> P [p,q] x;
    \<And>p q r ps x. quasi_sturm_seq (p#q#r#ps) \<Longrightarrow>
       \<lbrakk>poly p x \<noteq> 0 \<Longrightarrow> poly q x = 0 \<Longrightarrow> P (r#ps) x;
        poly q x \<noteq> 0 \<Longrightarrow> P (q#r#ps) x;
        poly p x = 0 \<Longrightarrow> P (q#r#ps) x\<rbrakk>
           \<Longrightarrow> P (p#q#r#ps) x\<rbrakk> \<Longrightarrow> P ps x"
proof goal_cases
  case prems: 1
  have "quasi_sturm_seq ps" ..
  with prems show ?thesis
  proof (induction ps x rule: split_sign_changes.induct)
    case (3 p q r ps x)
      show ?case
      proof (rule 3(5)[OF 3(6)])
        assume A: "poly p x \<noteq> 0" "poly q x = 0"
        from 3(6) have "quasi_sturm_seq (r#ps)"
            by (force dest: quasi_sturm_seq_Cons)
        with 3 A show "P (r # ps) x" by blast
      next
        assume A: "poly q x \<noteq> 0"
        from 3(6) have "quasi_sturm_seq (q#r#ps)"
            by (force dest: quasi_sturm_seq_Cons)
        with 3 A show "P (q # r # ps) x" by blast
      next
        assume A: "poly p x = 0"
        from 3(6) have "quasi_sturm_seq (q#r#ps)"
            by (force dest: quasi_sturm_seq_Cons)
        with 3 A show "P (q # r # ps) x" by blast
      qed
  qed simp_all
qed

text {*
  The total number of sign changes in the split list is the same
  as the number of sign changes in the original list.
*}
lemma (in quasi_sturm_seq) split_sign_changes_correct:
  assumes "poly (hd ps) x\<^sub>0 \<noteq> 0"
  defines "sign_changes' \<equiv> \<lambda>ps x.
               \<Sum>ps'\<leftarrow>split_sign_changes ps x. sign_changes ps' x"
  shows "sign_changes' ps x\<^sub>0 = sign_changes ps x\<^sub>0"
using assms(1)
proof (induction x\<^sub>0 rule: split_sign_changes_induct)
case (3 p q r ps x\<^sub>0)
  hence "poly p x\<^sub>0 \<noteq> 0" by simp
  note IH = 3(2,3,4)
  show ?case
  proof (cases "poly q x\<^sub>0 = 0")
    case True
      from 3 interpret quasi_sturm_seq "p#q#r#ps" by simp
      from signs[of 0] and True have
           sgn_r_x0: "poly r x\<^sub>0 * poly p x\<^sub>0 < 0" by simp
      with 3 have "poly r x\<^sub>0 \<noteq> 0" by force
      from sign_changes_distrib[OF this, of "[p,q]" ps]
        have "sign_changes (p#q#r#ps) x\<^sub>0 =
                  sign_changes ([p, q, r]) x\<^sub>0 + sign_changes (r # ps) x\<^sub>0" by simp
      also have "sign_changes (r#ps) x\<^sub>0 = sign_changes' (r#ps) x\<^sub>0"
          using `poly q x\<^sub>0 = 0` `poly p x\<^sub>0 \<noteq> 0` 3(5)`poly r x\<^sub>0 \<noteq> 0`
          by (intro IH(1)[symmetric], simp_all)
      finally show ?thesis unfolding sign_changes'_def
          using True `poly p x\<^sub>0 \<noteq> 0` by simp
  next
    case False
      from sign_changes_distrib[OF this, of "[p]" "r#ps"]
          have "sign_changes (p#q#r#ps) x\<^sub>0 =
                  sign_changes ([p,q]) x\<^sub>0 + sign_changes (q#r#ps) x\<^sub>0" by simp
      also have "sign_changes (q#r#ps) x\<^sub>0 = sign_changes' (q#r#ps) x\<^sub>0"
          using `poly q x\<^sub>0 \<noteq> 0` `poly p x\<^sub>0 \<noteq> 0` 3(5)
          by (intro IH(2)[symmetric], simp_all)
      finally show ?thesis unfolding sign_changes'_def
          using False by simp
    qed
qed (simp_all add: sign_changes_def sign_changes'_def)


text {*
  We now prove that if $p(x)\neq 0$, the number of sign changes of a Sturm sequence of $p$
  at $x$ is constant in a neighbourhood of $x$.
*}

lemma (in quasi_sturm_seq) split_sign_changes_correct_nbh:
  assumes "poly (hd ps) x\<^sub>0 \<noteq> 0"
  defines "sign_changes' \<equiv> \<lambda>x\<^sub>0 ps x.
               \<Sum>ps'\<leftarrow>split_sign_changes ps x\<^sub>0. sign_changes ps' x"
  shows "eventually (\<lambda>x. sign_changes' x\<^sub>0 ps x = sign_changes ps x) (at x\<^sub>0)"
proof (rule eventually_mono)
  show "eventually (\<lambda>x. \<forall>p\<in>{p \<in> set ps. poly p x\<^sub>0 \<noteq> 0}. sgn (poly p x) = sgn (poly p x\<^sub>0)) (at x\<^sub>0)"
      by (rule eventually_ball_finite, auto intro: poly_neighbourhood_same_sign)
next
  fix x
  show "(\<forall>p\<in>{p \<in> set ps. poly p x\<^sub>0 \<noteq> 0}. sgn (poly p x) = sgn (poly p x\<^sub>0)) \<Longrightarrow>
        sign_changes' x\<^sub>0 ps x = sign_changes ps x"
  proof -
    fix x assume nbh: "\<forall>p\<in>{p \<in> set ps. poly p x\<^sub>0 \<noteq> 0}. sgn (poly p x) = sgn (poly p x\<^sub>0)"
    thus "sign_changes' x\<^sub>0 ps x = sign_changes ps x" using assms(1)
    proof (induction x\<^sub>0 rule: split_sign_changes_induct)
    case (3 p q r ps x\<^sub>0)
      hence "poly p x\<^sub>0 \<noteq> 0" by simp
      note IH = 3(2,3,4)
      show ?case
      proof (cases "poly q x\<^sub>0 = 0")
        case True
          from 3 interpret quasi_sturm_seq "p#q#r#ps" by simp
          from signs[of 0] and True have
               sgn_r_x0: "poly r x\<^sub>0 * poly p x\<^sub>0 < 0" by simp
          with 3 have "poly r x\<^sub>0 \<noteq> 0" by force
          with nbh 3(5) have "poly r x \<noteq> 0" by (auto simp: sgn_zero_iff)
          from sign_changes_distrib[OF this, of "[p,q]" ps]
            have "sign_changes (p#q#r#ps) x =
                      sign_changes ([p, q, r]) x + sign_changes (r # ps) x" by simp
          also have "sign_changes (r#ps) x = sign_changes' x\<^sub>0 (r#ps) x"
              using `poly q x\<^sub>0 = 0` nbh `poly p x\<^sub>0 \<noteq> 0` 3(5)`poly r x\<^sub>0 \<noteq> 0`
              by (intro IH(1)[symmetric], simp_all)
          finally show ?thesis unfolding sign_changes'_def
              using True `poly p x\<^sub>0 \<noteq> 0`by simp
      next
        case False
          with nbh 3(5) have "poly q x \<noteq> 0" by (auto simp: sgn_zero_iff)
          from sign_changes_distrib[OF this, of "[p]" "r#ps"]
              have "sign_changes (p#q#r#ps) x =
                      sign_changes ([p,q]) x + sign_changes (q#r#ps) x" by simp
          also have "sign_changes (q#r#ps) x = sign_changes' x\<^sub>0 (q#r#ps) x"
              using `poly q x\<^sub>0 \<noteq> 0` nbh `poly p x\<^sub>0 \<noteq> 0` 3(5)
              by (intro IH(2)[symmetric], simp_all)
          finally show ?thesis unfolding sign_changes'_def
              using False by simp
        qed
    qed (simp_all add: sign_changes_def sign_changes'_def)
  qed
qed



lemma (in quasi_sturm_seq) hd_nonzero_imp_sign_changes_const_aux:
  assumes "poly (hd ps) x\<^sub>0 \<noteq> 0" and "ps' \<in> set (split_sign_changes ps x\<^sub>0)"
  shows "eventually (\<lambda>x. sign_changes ps' x = sign_changes ps' x\<^sub>0) (at x\<^sub>0)"
using assms
proof (induction x\<^sub>0 rule: split_sign_changes_induct)
  case (1 p x)
    thus ?case by (simp add: sign_changes_def)
next
  case (2 p q x\<^sub>0)
    hence [simp]: "ps' = [p,q]" by simp
    from 2 have "poly p x\<^sub>0 \<noteq> 0" by simp
    from 2(1) interpret quasi_sturm_seq "[p,q]" .
    from poly_neighbourhood_same_sign[OF `poly p x\<^sub>0 \<noteq> 0`]
        have "eventually (\<lambda>x. sgn (poly p x) = sgn (poly p x\<^sub>0)) (at x\<^sub>0)" .
    moreover from last_ps_sgn_const
        have sgn_q: "\<And>x. sgn (poly q x) = sgn (poly q x\<^sub>0)" by simp
    ultimately have A:  "eventually (\<lambda>x. \<forall>p\<in>set[p,q]. sgn (poly p x) =
                           sgn (poly p x\<^sub>0)) (at x\<^sub>0)" by simp
    thus ?case by (force intro: eventually_mono[OF A]
                                sign_changes_cong')
next
  case (3 p q r ps'' x\<^sub>0)
    hence p_not_0: "poly p x\<^sub>0 \<noteq> 0" by simp
    note sturm = 3(1)
    note IH = 3(2,3)
    note ps''_props = 3(6)
    show ?case
    proof (cases "poly q x\<^sub>0 = 0")
      case True
        note q_0 = this
        from sturm interpret quasi_sturm_seq "p#q#r#ps''" .
        from signs[of 0] and q_0
            have signs': "poly r x\<^sub>0 * poly p x\<^sub>0 < 0" by simp
        with p_not_0 have r_not_0: "poly r x\<^sub>0 \<noteq> 0" by force
        show ?thesis
        proof (cases "ps' \<in> set (split_sign_changes (r # ps'') x\<^sub>0)")
          case True
            show ?thesis by (rule IH(1), fact, fact, simp add: r_not_0, fact)
        next
          case False
            with ps''_props p_not_0 q_0 have ps'_props: "ps' = [p,q,r]" by simp
            from signs[of 0] and q_0
                have sgn_r: "poly r x\<^sub>0 * poly p x\<^sub>0 < 0" by simp
            from p_not_0 sgn_r
              have A: "eventually (\<lambda>x. sgn (poly p x) = sgn (poly p x\<^sub>0) \<and>
                                     sgn (poly r x) = sgn (poly r x\<^sub>0)) (at x\<^sub>0)"
                  by (intro eventually_conj poly_neighbourhood_same_sign,
                      simp_all add: r_not_0)
            show ?thesis
            proof (rule eventually_mono[OF A], clarify,
                   subst ps'_props, subst sign_changes_sturm_triple)
              fix x assume A: "sgn (poly p x) = sgn (poly p x\<^sub>0)"
                       and B: "sgn (poly r x) = sgn (poly r x\<^sub>0)"
              have prod_neg: "\<And>a (b::real). \<lbrakk>a>0; b>0; a*b<0\<rbrakk> \<Longrightarrow> False"
                             "\<And>a (b::real). \<lbrakk>a<0; b<0; a*b<0\<rbrakk> \<Longrightarrow> False"
                  by (drule mult_pos_pos, simp, simp,
                      drule mult_neg_neg, simp, simp)
              from A and `poly p x\<^sub>0 \<noteq> 0` show "poly p x \<noteq> 0"
                  by (force simp: sgn_zero_iff)

              with sgn_r p_not_0 r_not_0 A B
                  have "poly r x * poly p x < 0" "poly r x \<noteq> 0"
                  by (metis sgn_less sgn_times, metis sgn_0_0)
              with sgn_r show sgn_r': "sgn (poly r x) = - sgn (poly p x)"
                  apply (simp add: sgn_real_def not_le not_less
                             split: split_if_asm, intro conjI impI)
                  using prod_neg[of "poly r x" "poly p x"] apply force+
                  done

              show "1 = sign_changes ps' x\<^sub>0"
                  by (subst ps'_props, subst sign_changes_sturm_triple,
                      fact, metis A B sgn_r', simp)
            qed
        qed
    next
      case False
        note q_not_0 = this
        show ?thesis
        proof (cases "ps' \<in> set (split_sign_changes (q # r # ps'') x\<^sub>0)")
          case True
            show ?thesis by (rule IH(2), fact, simp add: q_not_0, fact)
        next
          case False
            with ps''_props and q_not_0 have "ps' = [p, q]" by simp
            hence [simp]: "\<forall>p\<in>set ps'. poly p x\<^sub>0 \<noteq> 0"
                using q_not_0 p_not_0 by simp
            show ?thesis
            proof (rule eventually_mono)
              fix x assume "\<forall>p\<in>set ps'. sgn (poly p x) = sgn (poly p x\<^sub>0)"
              thus "sign_changes ps' x = sign_changes ps' x\<^sub>0"
                  by (rule sign_changes_cong')
            next
              show "eventually (\<lambda>x. \<forall>p\<in>set ps'.
                        sgn (poly p x) = sgn (poly p x\<^sub>0)) (at x\<^sub>0)"
                  by (force intro: eventually_ball_finite
                                   poly_neighbourhood_same_sign)
            qed
    qed
  qed
qed


lemma (in quasi_sturm_seq) hd_nonzero_imp_sign_changes_const:
  assumes "poly (hd ps) x\<^sub>0 \<noteq> 0"
  shows "eventually (\<lambda>x. sign_changes ps x = sign_changes ps x\<^sub>0) (at x\<^sub>0)"
proof-
  let ?pss = "split_sign_changes ps x\<^sub>0"
  let ?f = "\<lambda>pss x. \<Sum>ps'\<leftarrow>pss. sign_changes ps' x"
  {
    fix pss assume "\<And>ps'. ps'\<in>set pss \<Longrightarrow>
        eventually (\<lambda>x. sign_changes ps' x = sign_changes ps' x\<^sub>0) (at x\<^sub>0)"
    hence "eventually (\<lambda>x. ?f pss x = ?f pss x\<^sub>0) (at x\<^sub>0)"
    proof (induction pss)
      case (Cons ps' pss)
      then show ?case
        apply (rule eventually_mono[OF eventually_conj])
        apply (auto simp add: Cons.prems)
        done
    qed simp
  }
  note A = this[of ?pss]
  have B: "eventually (\<lambda>x. ?f ?pss x = ?f ?pss x\<^sub>0) (at x\<^sub>0)"
      by (rule A, rule hd_nonzero_imp_sign_changes_const_aux[OF assms], simp)
  note C = split_sign_changes_correct_nbh[OF assms]
  note D = split_sign_changes_correct[OF assms]
  note E = eventually_conj[OF B C]
  show ?thesis by (rule eventually_mono[OF E], auto simp: D)
qed

(*<*)
hide_fact quasi_sturm_seq.split_sign_changes_correct_nbh
hide_fact quasi_sturm_seq.hd_nonzero_imp_sign_changes_const_aux
(*>*)

lemma (in sturm_seq) p_nonzero_imp_sign_changes_const:
  "poly p x\<^sub>0 \<noteq> 0 \<Longrightarrow>
       eventually (\<lambda>x. sign_changes ps x = sign_changes ps x\<^sub>0) (at x\<^sub>0)"
  using hd_nonzero_imp_sign_changes_const by simp


text {*
  If $x$ is a root of $p$ and $p$ is not the zero polynomial, the
  number of sign changes of a Sturm chain of $p$ decreases by 1 at $x$.
*}
lemma (in sturm_seq) p_zero:
  assumes "poly p x\<^sub>0 = 0" "p \<noteq> 0"
  shows "eventually (\<lambda>x. sign_changes ps x =
      sign_changes ps x\<^sub>0 + (if x<x\<^sub>0 then 1 else 0)) (at x\<^sub>0)"
proof-
  from ps_first_two obtain q ps' where [simp]: "ps = p#q#ps'" .
  hence "ps!1 = q" by simp
  have "eventually (\<lambda>x. x \<noteq> x\<^sub>0) (at x\<^sub>0)"
      by (simp add: eventually_at, rule exI[of _ 1], simp)
  moreover from p_squarefree and assms(1) have "poly q x\<^sub>0 \<noteq> 0" by simp
  {
      have A: "quasi_sturm_seq ps" ..
      with quasi_sturm_seq_Cons[of p "q#ps'"]
          interpret quasi_sturm_seq "q#ps'" by simp
      from `poly q x\<^sub>0 \<noteq> 0` have "eventually (\<lambda>x. sign_changes (q#ps') x =
                                     sign_changes (q#ps') x\<^sub>0) (at x\<^sub>0)"
      using hd_nonzero_imp_sign_changes_const[where x\<^sub>0=x\<^sub>0] by simp
  }
  moreover note poly_neighbourhood_without_roots[OF assms(2)] deriv[OF assms(1)]
  ultimately
      have A: "eventually (\<lambda>x. x \<noteq> x\<^sub>0 \<and> poly p x \<noteq> 0 \<and>
                   sgn (poly (p*ps!1) x) = (if x > x\<^sub>0 then 1 else -1) \<and>
                   sign_changes (q#ps') x = sign_changes (q#ps') x\<^sub>0) (at x\<^sub>0)"
           by (simp only: `ps!1 = q`, intro eventually_conj)
  show ?thesis
  proof (rule eventually_mono[OF A], clarify, goal_cases)
    case prems: (1 x)
    from zero_less_mult_pos have zero_less_mult_pos':
        "\<And>a b. \<lbrakk>(0::real) < a*b; 0 < b\<rbrakk> \<Longrightarrow> 0 < a"
        by (subgoal_tac "a*b = b*a", auto)
    from prems have "poly q x \<noteq> 0" and q_sgn: "sgn (poly q x) =
              (if x < x\<^sub>0 then -sgn (poly p x) else sgn (poly p x))"
        by (auto simp add: sgn_real_def elim: linorder_neqE_linordered_idom
                 dest: mult_neg_neg zero_less_mult_pos
                 zero_less_mult_pos' split: split_if_asm)
     from sign_changes_distrib[OF `poly q x \<noteq> 0`, of "[p]" ps']
        have "sign_changes ps x = sign_changes [p,q] x + sign_changes (q#ps') x"
            by simp
    also from q_sgn and `poly p x \<noteq> 0`
        have "sign_changes [p,q] x = (if x<x\<^sub>0 then 1 else 0)"
        by (simp add: sign_changes_def sgn_zero_iff split: split_if_asm)
    also note prems(4)
    also from assms(1) have "sign_changes (q#ps') x\<^sub>0 = sign_changes ps x\<^sub>0"
        by (simp add: sign_changes_def)
    finally show ?case by simp
  qed
qed

text {*
  With these two results, we can now show that if $p$ is nonzero, the number
  of roots in an interval of the form $(a;b]$ is the difference of the sign changes
  of a Sturm sequence of $p$ at $a$ and $b$.\\
  First, however, we prove the following auxiliary lemma that shows that
  if a function $f: \RR\to\NN$ is locally constant at any $x\in(a;b]$, it is constant
  across the entire interval $(a;b]$:
*}

lemma count_roots_between_aux:
  assumes "a \<le> b"
  assumes "\<forall>x::real. a < x \<and> x \<le> b \<longrightarrow> eventually (\<lambda>\<xi>. f \<xi> = (f x::nat)) (at x)"
  shows "\<forall>x. a < x \<and> x \<le> b \<longrightarrow> f x = f b"
proof (clarify)
  fix x assume "x > a" "x \<le> b"
  with assms have "\<forall>x'. x \<le> x' \<and> x' \<le> b \<longrightarrow>
                       eventually (\<lambda>\<xi>. f \<xi> = f x') (at x')" by auto
  from fun_eq_in_ivl[OF `x \<le> b` this] show "f x = f b" .
qed

text {*
  Now we can prove the actual root-counting theorem:
*}
theorem (in sturm_seq) count_roots_between:
  assumes [simp]: "p \<noteq> 0" "a \<le> b"
  shows "sign_changes ps a - sign_changes ps b =
             card {x. x > a \<and> x \<le> b \<and> poly p x = 0}"
proof-
  have "sign_changes ps a - int (sign_changes ps b) =
             card {x. x > a \<and> x \<le> b \<and> poly p x = 0}" using `a \<le> b`
  proof (induction "card {x. x > a \<and> x \<le> b \<and> poly p x = 0}" arbitrary: a b
             rule: less_induct)
    case (less a b)
      show ?case
      proof (cases "\<exists>x. a < x \<and> x \<le> b \<and> poly p x = 0")
        case False
          hence no_roots: "{x. a < x \<and> x \<le> b \<and> poly p x = 0} = {}"
              (is "?roots=_") by auto
          hence card_roots: "card ?roots = (0::int)" by (subst no_roots, simp)
          show ?thesis
          proof (simp only: card_roots eq_iff_diff_eq_0[symmetric] of_nat_eq_iff,
                 cases "poly p a = 0")
            case False
              with no_roots show "sign_changes ps a = sign_changes ps b"
                  by (force intro: fun_eq_in_ivl `a \<le> b`
                                   p_nonzero_imp_sign_changes_const)
          next
            case True
              have A: "\<forall>x. a < x \<and> x \<le> b \<longrightarrow> sign_changes ps x = sign_changes ps b"
                  apply (rule count_roots_between_aux, fact, clarify)
                  apply (rule p_nonzero_imp_sign_changes_const)
                  apply (insert False, simp)
                  done
              have "eventually (\<lambda>x. x > a \<longrightarrow>
                        sign_changes ps x = sign_changes ps a) (at a)"
                  apply (rule eventually_mono [OF p_zero[OF `poly p a = 0` `p \<noteq> 0`]])
                  apply force
                  done
              then obtain \<delta> where \<delta>_props:
                  "\<delta> > 0" "\<forall>x. x > a \<and> x < a+\<delta> \<longrightarrow>
                                   sign_changes ps x = sign_changes ps a"
                  by (auto simp: eventually_at dist_real_def)

              show "sign_changes ps a = sign_changes ps b"
              proof (cases "a = b")
                case False
                  def x \<equiv> "min (a+\<delta>/2) b"
                  with False have "a < x" "x < a+\<delta>" "x \<le> b"
                     using `\<delta> > 0` `a \<le> b` by simp_all
                  from \<delta>_props `a < x` `x < a+\<delta>`
                      have "sign_changes ps a = sign_changes ps x" by simp
                  also from A `a < x` `x \<le> b` have "... = sign_changes ps b"
                      by blast
                  finally show ?thesis .
              qed simp
          qed

      next
        case True
          from poly_roots_finite[OF assms(1)]
            have fin: "finite {x. x > a \<and> x \<le> b \<and> poly p x = 0}"
            by (force intro: finite_subset)
          from True have "{x. x > a \<and> x \<le> b \<and> poly p x = 0} \<noteq> {}" by blast
          with fin have card_greater_0:
              "card {x. x > a \<and> x \<le> b \<and> poly p x = 0} > 0" by fastforce

          def x\<^sub>2 \<equiv> "Min {x. x > a \<and> x \<le> b \<and> poly p x = 0}"
          from Min_in[OF fin] and True
              have x\<^sub>2_props: "x\<^sub>2 > a" "x\<^sub>2 \<le> b" "poly p x\<^sub>2 = 0"
              unfolding x\<^sub>2_def by blast+
          from Min_le[OF fin] x\<^sub>2_props
              have x\<^sub>2_le: "\<And>x'. \<lbrakk>x' > a; x' \<le> b; poly p x' = 0\<rbrakk> \<Longrightarrow> x\<^sub>2 \<le> x'"
              unfolding x\<^sub>2_def by simp

          have left: "{x. a < x \<and> x \<le> x\<^sub>2 \<and> poly p x = 0} = {x\<^sub>2}"
              using x\<^sub>2_props x\<^sub>2_le by force
          hence [simp]: "card {x. a < x \<and> x \<le> x\<^sub>2 \<and> poly p x = 0} = 1" by simp

          from p_zero[OF `poly p x\<^sub>2 = 0` `p \<noteq> 0`,
              unfolded eventually_at dist_real_def] guess \<epsilon> ..
          hence \<epsilon>_props: "\<epsilon> > 0"
              "\<forall>x. x \<noteq> x\<^sub>2 \<and> \<bar>x - x\<^sub>2\<bar> < \<epsilon> \<longrightarrow>
                   sign_changes ps x = sign_changes ps x\<^sub>2 +
                       (if x < x\<^sub>2 then 1 else 0)" by auto
          def x\<^sub>1 \<equiv> "max (x\<^sub>2 - \<epsilon> / 2) a"
          have "\<bar>x\<^sub>1 - x\<^sub>2\<bar> < \<epsilon>" using `\<epsilon> > 0` x\<^sub>2_props by (simp add: x\<^sub>1_def)
          hence "sign_changes ps x\<^sub>1 =
              (if x\<^sub>1 < x\<^sub>2 then sign_changes ps x\<^sub>2 + 1 else sign_changes ps x\<^sub>2)"
              using \<epsilon>_props(2) by (cases "x\<^sub>1 = x\<^sub>2", auto)
          hence "sign_changes ps x\<^sub>1 - sign_changes ps x\<^sub>2 = 1"
              unfolding x\<^sub>1_def using x\<^sub>2_props `\<epsilon> > 0` by simp

          also have "x\<^sub>2 \<notin> {x. a < x \<and> x \<le> x\<^sub>1 \<and> poly p x = 0}"
              unfolding x\<^sub>1_def using `\<epsilon> > 0` by force
          with left have "{x. a < x \<and> x \<le> x\<^sub>1 \<and> poly p x = 0} = {}" by force
          with less(1)[of a x\<^sub>1] have "sign_changes ps x\<^sub>1 = sign_changes ps a"
              unfolding x\<^sub>1_def `\<epsilon> > 0` by (force simp: card_greater_0)

          finally have signs_left:
              "sign_changes ps a - int (sign_changes ps x\<^sub>2) = 1" by simp

          have "{x. x > a \<and> x \<le> b \<and> poly p x = 0} =
                {x. a < x \<and> x \<le> x\<^sub>2 \<and> poly p x = 0} \<union>
                {x. x\<^sub>2 < x \<and> x \<le> b \<and> poly p x = 0}" using x\<^sub>2_props by auto
          also note left
          finally have A: "card {x. x\<^sub>2 < x \<and> x \<le> b \<and> poly p x = 0} + 1 =
              card {x. a < x \<and> x \<le> b \<and> poly p x = 0}" using fin by simp
          hence "card {x. x\<^sub>2 < x \<and> x \<le> b \<and> poly p x = 0} <
                 card {x. a < x \<and> x \<le> b \<and> poly p x = 0}" by simp
          from less(1)[OF this x\<^sub>2_props(2)] and A
              have signs_right: "sign_changes ps x\<^sub>2 - int (sign_changes ps b) + 1 =
                  card {x. a < x \<and> x \<le> b \<and> poly p x = 0}" by simp

          from signs_left and signs_right show ?thesis by simp
        qed
  qed
  thus ?thesis by simp
qed

text {*
  By applying this result to a sufficiently large upper bound, we can effectively count
  the number of roots ``between $a$ and infinity'', i.\,e. the roots greater than $a$:
*}
lemma (in sturm_seq) count_roots_above:
  assumes "p \<noteq> 0"
  shows "sign_changes ps a - sign_changes_inf ps =
             card {x. x > a \<and> poly p x = 0}"
proof-
  have "p \<in> set ps" using hd_in_set[OF ps_not_Nil] by simp
  have "finite (set ps)" by simp
  from polys_inf_sign_thresholds[OF this] guess l u .
  note lu_props = this
  let ?u = "max a u"
  {fix x assume "poly p x = 0" hence "x \<le> ?u"
   using lu_props(3)[OF `p \<in> set ps`, of x] `p \<noteq> 0`
       by (cases "u \<le> x", auto simp: sgn_zero_iff)
  } note [simp] = this

  from lu_props
    have "map (\<lambda>p. sgn (poly p ?u)) ps = map poly_inf ps" by simp
  hence "sign_changes ps a - sign_changes_inf ps =
             sign_changes ps a - sign_changes ps ?u"
      by (simp_all only: sign_changes_def sign_changes_inf_def)
  also from count_roots_between[OF assms] lu_props
      have "... =  card {x. a < x \<and> x \<le> ?u \<and> poly p x = 0}" by simp
  also have "{x. a < x \<and> x \<le> ?u \<and> poly p x = 0} = {x. a < x \<and> poly p x = 0}"
      using lu_props by auto
  finally show ?thesis .
qed

text {*
  The same works analogously for the number of roots below $a$ and the
  total number of roots.
*}

lemma (in sturm_seq) count_roots_below:
  assumes "p \<noteq> 0"
  shows "sign_changes_neg_inf ps - sign_changes ps a =
             card {x. x \<le> a \<and> poly p x = 0}"
proof-
  have "p \<in> set ps" using hd_in_set[OF ps_not_Nil] by simp
  have "finite (set ps)" by simp
  from polys_inf_sign_thresholds[OF this] guess l u .
  note lu_props = this
  let ?l = "min a l"
  {fix x assume "poly p x = 0" hence "x > ?l"
   using lu_props(4)[OF `p \<in> set ps`, of x] `p \<noteq> 0`
       by (cases "l < x", auto simp: sgn_zero_iff)
  } note [simp] = this

  from lu_props
    have "map (\<lambda>p. sgn (poly p ?l)) ps = map poly_neg_inf ps" by simp
  hence "sign_changes_neg_inf ps - sign_changes ps a =
             sign_changes ps ?l - sign_changes ps a"
      by (simp_all only: sign_changes_def sign_changes_neg_inf_def)
  also from count_roots_between[OF assms] lu_props
      have "... =  card {x. ?l < x \<and> x \<le> a \<and> poly p x = 0}" by simp
  also have "{x. ?l < x \<and> x \<le> a \<and> poly p x = 0} = {x. a \<ge> x \<and> poly p x = 0}"
      using lu_props by auto
  finally show ?thesis .
qed

lemma (in sturm_seq) count_roots:
  assumes "p \<noteq> 0"
  shows "sign_changes_neg_inf ps - sign_changes_inf ps =
             card {x. poly p x = 0}"
proof-
  have "finite (set ps)" by simp
  from polys_inf_sign_thresholds[OF this] guess l u .
  note lu_props = this

  from lu_props
    have "map (\<lambda>p. sgn (poly p l)) ps = map poly_neg_inf ps"
         "map (\<lambda>p. sgn (poly p u)) ps = map poly_inf ps" by simp_all
  hence "sign_changes_neg_inf ps - sign_changes_inf ps =
             sign_changes ps l - sign_changes ps u"
      by (simp_all only: sign_changes_def sign_changes_inf_def
                         sign_changes_neg_inf_def)
  also from count_roots_between[OF assms] lu_props
      have "... =  card {x. l < x \<and> x \<le> u \<and> poly p x = 0}" by simp
  also have "{x. l < x \<and> x \<le> u \<and> poly p x = 0} = {x. poly p x = 0}"
      using lu_props assms by simp
  finally show ?thesis .
qed



subsection {* Constructing Sturm sequences *}

subsection {* The canonical Sturm sequence *}

text {*
  In this subsection, we will present the canonical Sturm sequence construction for
  a polynomial $p$ without multiple roots that is very similar to the Euclidean
  algorithm:
  $$p_i = \begin{cases}
    p & \text{for}\ i = 1\\
    p' & \text{for}\ i = 2\\
    -p_{i-2}\ \text{mod}\ p_{i-1} & \text{otherwise}
  \end{cases}$$
  We break off the sequence at the first constant polynomial.
*}

(*<*)
lemma degree_mod_less': "degree q \<noteq> 0 \<Longrightarrow> degree (p mod q) < degree q"
  by (metis degree_0 degree_mod_less not_gr0)
(*>*)

function sturm_aux where
"sturm_aux (p :: real poly) q =
    (if degree q = 0 then [p,q] else p # sturm_aux q (-(p mod q)))"
  by (pat_completeness, simp_all)
termination by (relation "measure (degree \<circ> snd)",
                simp_all add: o_def degree_mod_less')

(*<*)
declare sturm_aux.simps[simp del]
(*>*)

definition sturm where "sturm p = sturm_aux p (pderiv p)"

text {* Next, we show some simple facts about this construction: *}

lemma sturm_0[simp]: "sturm 0 = [0,0]"
    by (unfold sturm_def, subst sturm_aux.simps, simp)

lemma [simp]: "sturm_aux p q = [] \<longleftrightarrow> False"
    by (induction p q rule: sturm_aux.induct, subst sturm_aux.simps, auto)

lemma sturm_neq_Nil[simp]: "sturm p \<noteq> []" unfolding sturm_def by simp

lemma [simp]: "hd (sturm p) = p"
  unfolding sturm_def by (subst sturm_aux.simps, simp)

lemma [simp]: "p \<in> set (sturm p)"
  using hd_in_set[OF sturm_neq_Nil] by simp

lemma [simp]: "length (sturm p) \<ge> 2"
proof-
  {fix q have "length (sturm_aux p q) \<ge> 2"
           by (induction p q rule: sturm_aux.induct, subst sturm_aux.simps, auto)
  }
  thus ?thesis unfolding sturm_def .
qed

lemma [simp]: "degree (last (sturm p)) = 0"
proof-
  {fix q have "degree (last (sturm_aux p q)) = 0"
           by (induction p q rule: sturm_aux.induct, subst sturm_aux.simps, simp)
  }
  thus ?thesis unfolding sturm_def .
qed

lemma [simp]: "sturm_aux p q ! 0 = p"
    by (subst sturm_aux.simps, simp)
lemma [simp]: "sturm_aux p q ! Suc 0 = q"
    by (subst sturm_aux.simps, simp)

lemma [simp]: "sturm p ! 0 = p"
    unfolding sturm_def by simp
lemma [simp]: "sturm p ! Suc 0 = pderiv p"
    unfolding sturm_def by simp


lemma sturm_indices:
  assumes "i < length (sturm p) - 2"
  shows "sturm p!(i+2) = -(sturm p!i mod sturm p!(i+1))"
proof-
 {fix ps q
  have "\<lbrakk>ps = sturm_aux p q; i < length ps - 2\<rbrakk>
            \<Longrightarrow> ps!(i+2) = -(ps!i mod ps!(i+1))"
  proof (induction p q arbitrary: ps i rule: sturm_aux.induct)
    case (1 p q)
      show ?case
      proof (cases "i = 0")
        case False
          then obtain i' where [simp]: "i = Suc i'" by (cases i, simp_all)
          hence "length ps \<ge> 4" using 1 by simp
          with 1(2) have deg: "degree q \<noteq> 0"
              by (subst (asm) sturm_aux.simps, simp split: split_if_asm)
          with 1(2) obtain ps' where [simp]: "ps = p # ps'"
              by (subst (asm) sturm_aux.simps, simp)
          with 1(2) deg have ps': "ps' = sturm_aux q (-(p mod q))"
              by (subst (asm) sturm_aux.simps, simp)
          from `length ps \<ge> 4` and `ps = p # ps'` 1(3) False
              have "i - 1 < length ps' - 2" by simp
          from 1(1)[OF deg ps' this]
              show ?thesis by simp
      next
        case True
          with 1(3) have "length ps \<ge> 3" by simp
          with 1(2) have "degree q \<noteq> 0"
              by (subst (asm) sturm_aux.simps, simp split: split_if_asm)
          with 1(2) have [simp]: "sturm_aux p q ! Suc (Suc 0) = -(p mod q)"
              by (subst sturm_aux.simps, simp)
          from True have "ps!i = p" "ps!(i+1) = q" "ps!(i+2) = -(p mod q)"
              by (simp_all add: 1(2))
          thus ?thesis by simp
      qed
    qed}
  from this[OF sturm_def assms] show ?thesis .
qed

text {*
  If the Sturm sequence construction is applied to polynomials $p$ and $q$,
  the greatest common divisor of $p$ and $q$ a divisor of every element in the
  sequence. This is obvious from the similarity to Euclid's algorithm for
  computing the GCD.
*}

lemma sturm_aux_gcd: "r \<in> set (sturm_aux p q) \<Longrightarrow> gcd p q dvd r"
proof (induction p q rule: sturm_aux.induct)
  case (1 p q)
    show ?case
    proof (cases "r = p")
      case False
        with 1(2) have r: "r \<in> set (sturm_aux q (-(p mod q)))"
          by (subst (asm) sturm_aux.simps, simp split: split_if_asm,
              subst sturm_aux.simps, simp)
        show ?thesis
        proof (cases "degree q = 0")
          case False
            hence "q \<noteq> 0" by force
            from 1(1)[OF False r] show ?thesis
                by (subst gcd_poly.simps(2)[OF `q \<noteq> 0`], simp)
        next
          case True
            with 1(2) and `r \<noteq> p` have "r = q"
                by (subst (asm) sturm_aux.simps, simp)
            thus ?thesis by simp
        qed
    qed simp
qed

lemma sturm_gcd: "r \<in> set (sturm p) \<Longrightarrow> gcd p (pderiv p) dvd r"
    unfolding sturm_def by (rule sturm_aux_gcd)

text {*
  If two adjacent polynomials in the result of the canonical Sturm chain construction
  both have a root at some $x$, this $x$ is a root of all polynomials in the sequence.
*}

lemma sturm_adjacent_root_propagate_left:
  assumes "i < length (sturm (p :: real poly)) - 1"
  assumes "poly (sturm p ! i) x = 0"
      and "poly (sturm p ! (i + 1)) x = 0"
  shows "\<forall>j\<le>i+1. poly (sturm p ! j) x = 0"
using assms(2)
proof (intro sturm_adjacent_root_aux[OF assms(1,2,3)], goal_cases)
  case prems: (1 i x)
    let ?p = "sturm p ! i"
    let ?q = "sturm p ! (i + 1)"
    let ?r = "sturm p ! (i + 2)"
    from sturm_indices[OF prems(2)] have "?p = ?p div ?q * ?q - ?r"
        by (simp add: mod_div_equality)
    hence "poly ?p x = poly (?p div ?q * ?q - ?r) x" by simp
    hence "poly ?p x = -poly ?r x" using prems(3) by simp
    thus ?case by (simp add: sgn_minus)
qed

text {*
  Consequently, if this is the case in the canonical Sturm chain of $p$,
  $p$ must have multiple roots.
*}
lemma sturm_adjacent_root_not_squarefree:
  assumes "i < length (sturm (p :: real poly)) - 1"
          "poly (sturm p ! i) x = 0" "poly (sturm p ! (i + 1)) x = 0"
  shows "\<not>rsquarefree p"
proof-
  from sturm_adjacent_root_propagate_left[OF assms]
      have "poly p x = 0" "poly (pderiv p) x = 0" by auto
  thus ?thesis by (auto simp: rsquarefree_roots)
qed


text {*
  Since the second element of the sequence is chosen to be the derivative of $p$,
  $p_1$ and $p_2$ fulfil the property demanded by the definition of a Sturm sequence
  that they locally have opposite sign left of a root $x$ of $p$ and the same sign
  to the right of $x$.
*}

lemma sturm_firsttwo_signs_aux:
  assumes "(p :: real poly) \<noteq> 0" "q \<noteq> 0"
  assumes q_pderiv:
      "eventually (\<lambda>x. sgn (poly q x) = sgn (poly (pderiv p) x)) (at x\<^sub>0)"
  assumes p_0: "poly p (x\<^sub>0::real) = 0"
  shows "eventually (\<lambda>x. sgn (poly (p*q) x) = (if x > x\<^sub>0 then 1 else -1)) (at x\<^sub>0)"
proof-
  have A: "eventually (\<lambda>x. poly p x \<noteq> 0 \<and> poly q x \<noteq> 0 \<and>
               sgn (poly q x) = sgn (poly (pderiv p) x)) (at x\<^sub>0)"
      using `p \<noteq> 0`  `q \<noteq> 0`
      by (intro poly_neighbourhood_same_sign q_pderiv
                poly_neighbourhood_without_roots eventually_conj)
  then obtain \<epsilon> where \<epsilon>_props: "\<epsilon> > 0" "\<forall>x. x \<noteq> x\<^sub>0 \<and> \<bar>x - x\<^sub>0\<bar> < \<epsilon> \<longrightarrow>
      poly p x \<noteq> 0 \<and> poly q x \<noteq> 0 \<and> sgn (poly (pderiv p) x) = sgn (poly q x)"
      by (auto simp: eventually_at dist_real_def)
  have sqr_pos: "\<And>x::real. x \<noteq> 0 \<Longrightarrow> sgn x * sgn x = 1"
      by (auto simp: sgn_real_def)

  show ?thesis
  proof (simp only: eventually_at dist_real_def, rule exI[of _ \<epsilon>],
         intro conjI, fact `\<epsilon> > 0`, clarify)
    fix x assume "x \<noteq> x\<^sub>0" "\<bar>x - x\<^sub>0\<bar> < \<epsilon>"
    with \<epsilon>_props have [simp]: "poly p x \<noteq> 0" "poly q x \<noteq> 0"
        "sgn (poly (pderiv p) x) = sgn (poly q x)" by auto
    show "sgn (poly (p*q) x) = (if x > x\<^sub>0 then 1 else -1)"
    proof (cases "x \<ge> x\<^sub>0")
      case True
        with `x \<noteq> x\<^sub>0` have "x > x\<^sub>0" by simp
        from poly_MVT[OF this, of p] guess \<xi> ..
        note \<xi>_props = this
        with `\<bar>x - x\<^sub>0\<bar> < \<epsilon>` `poly p x\<^sub>0 = 0` `x > x\<^sub>0` \<epsilon>_props
            have "\<bar>\<xi> - x\<^sub>0\<bar> < \<epsilon>" "sgn (poly p x) = sgn (x - x\<^sub>0) * sgn (poly q \<xi>)"
            by (auto simp add: q_pderiv sgn_mult)
        moreover from \<xi>_props \<epsilon>_props `\<bar>x - x\<^sub>0\<bar> < \<epsilon>`
            have "\<forall>t. \<xi> \<le> t \<and> t \<le> x \<longrightarrow> poly q t \<noteq> 0" by auto
        hence "sgn (poly q \<xi>) = sgn (poly q x)" using \<xi>_props \<epsilon>_props
            by (intro no_roots_inbetween_imp_same_sign, simp_all)
        ultimately show ?thesis using True `x \<noteq> x\<^sub>0` \<epsilon>_props \<xi>_props
            by (auto simp: sgn_mult sqr_pos)
    next
      case False
        hence "x < x\<^sub>0" by simp
        hence sgn: "sgn (x - x\<^sub>0) = -1" by simp
        from poly_MVT[OF `x < x\<^sub>0`, of p] guess \<xi> ..
        note \<xi>_props = this
        with `\<bar>x - x\<^sub>0\<bar> < \<epsilon>` `poly p x\<^sub>0 = 0` `x < x\<^sub>0` \<epsilon>_props
            have "\<bar>\<xi> - x\<^sub>0\<bar> < \<epsilon>" "poly p x = (x - x\<^sub>0) * poly (pderiv p) \<xi>"
                 "poly p \<xi> \<noteq> 0" by (auto simp: field_simps)
        hence "sgn (poly p x) = sgn (x - x\<^sub>0) * sgn (poly q \<xi>)"
            using \<epsilon>_props \<xi>_props by (auto simp: q_pderiv sgn_mult)
        moreover from \<xi>_props \<epsilon>_props `\<bar>x - x\<^sub>0\<bar> < \<epsilon>`
            have "\<forall>t. x \<le> t \<and> t \<le> \<xi> \<longrightarrow> poly q t \<noteq> 0" by auto
        hence "sgn (poly q \<xi>) = sgn (poly q x)" using \<xi>_props \<epsilon>_props
            by (rule_tac sym, intro no_roots_inbetween_imp_same_sign, simp_all)
        ultimately show ?thesis using False `x \<noteq> x\<^sub>0`
            by (auto simp: sgn_mult sqr_pos)
    qed
  qed
qed

lemma sturm_firsttwo_signs:
  fixes ps :: "real poly list"
  assumes squarefree: "rsquarefree p"
  assumes p_0: "poly p (x\<^sub>0::real) = 0"
  shows "eventually (\<lambda>x. sgn (poly (p * sturm p ! 1) x) =
             (if x > x\<^sub>0 then 1 else -1)) (at x\<^sub>0)"
proof-
  from assms have [simp]: "p \<noteq> 0" by (auto simp add: rsquarefree_roots)
  with squarefree p_0 have [simp]: "pderiv p \<noteq> 0"
      by (auto simp  add:rsquarefree_roots)
  from assms show ?thesis
      by (intro sturm_firsttwo_signs_aux,
          simp_all add: rsquarefree_roots)
qed


text {*
  The construction also obviously fulfils the property about three
  adjacent polynomials in the sequence.
*}

lemma sturm_signs:
  assumes squarefree: "rsquarefree p"
  assumes i_in_range: "i < length (sturm (p :: real poly)) - 2"
  assumes q_0: "poly (sturm p ! (i+1)) x = 0" (is "poly ?q x = 0")
  shows "poly (sturm p ! (i+2)) x * poly (sturm p ! i) x < 0"
            (is "poly ?p x * poly ?r x < 0")
proof-
  from sturm_indices[OF i_in_range]
      have "sturm p ! (i+2) = - (sturm p ! i mod sturm p ! (i+1))"
           (is "?r = - (?p mod ?q)") .
  hence "-?r = ?p mod ?q" by simp
  with mod_div_equality[of ?p ?q] have "?p div ?q * ?q - ?r = ?p" by simp
  hence "poly (?p div ?q) x * poly ?q x - poly ?r x = poly ?p x"
      by (metis poly_diff poly_mult)
  with q_0 have r_x: "poly ?r x = -poly ?p x" by simp
  moreover have sqr_pos: "\<And>x::real. x \<noteq> 0 \<Longrightarrow> x * x > 0" apply (case_tac "x \<ge> 0")
      by (simp_all add: mult_neg_neg)
  from sturm_adjacent_root_not_squarefree[of i p] assms r_x
      have "poly ?p x * poly ?p x > 0" by (force intro: sqr_pos)
  ultimately show "poly ?r x * poly ?p x < 0" by simp
qed


text {*
  Finally, if $p$ contains no multiple roots, @{term "sturm p"}, i.e.
  the canonical Sturm sequence for $p$, is a Sturm sequence
  and can be used to determine the number of roots of $p$.
*}
lemma sturm_seq_sturm[simp]:
   assumes "rsquarefree p"
   shows "sturm_seq (sturm p) p"
proof
  show "sturm p \<noteq> []" by simp
  show "hd (sturm p) = p" by simp
  show "length (sturm p) \<ge> 2" by simp
  from assms show "\<And>x. \<not>(poly p x = 0 \<and> poly (sturm p ! 1) x = 0)"
      by (simp add: rsquarefree_roots)
next
  fix x :: real and y :: real
  have "degree (last (sturm p)) = 0" by simp
  then obtain c where "last (sturm p) = [:c:]"
      by (cases "last (sturm p)", simp split: split_if_asm)
  thus "\<And>x y. sgn (poly (last (sturm p)) x) =
            sgn (poly (last (sturm p)) y)" by simp
next
  from sturm_firsttwo_signs[OF assms]
    show "\<And>x\<^sub>0. poly p x\<^sub>0 = 0 \<Longrightarrow>
         eventually (\<lambda>x. sgn (poly (p*sturm p ! 1) x) =
                         (if x > x\<^sub>0 then 1 else -1)) (at x\<^sub>0)" by simp
next
  from sturm_signs[OF assms]
    show "\<And>i x. \<lbrakk>i < length (sturm p) - 2; poly (sturm p ! (i + 1)) x = 0\<rbrakk>
          \<Longrightarrow> poly (sturm p ! (i + 2)) x * poly (sturm p ! i) x < 0" by simp
qed


subsubsection {* Canonical squarefree Sturm sequence *}

text {*
  The previous construction does not work for polynomials with multiple roots,
  but we can simply ``divide away'' multiple roots by dividing $p$ by the
  GCD of $p$ and $p'$. The resulting polynomial has the same roots as $p$,
  but with multiplicity 1, allowing us to again use the canonical construction.
*}
definition sturm_squarefree where
  "sturm_squarefree p = sturm (p div (gcd p (pderiv p)))"

lemma sturm_squarefree_not_Nil[simp]: "sturm_squarefree p \<noteq> []"
  by (simp add: sturm_squarefree_def)


lemma sturm_seq_sturm_squarefree:
  assumes [simp]: "p \<noteq> 0"
  defines [simp]: "p' \<equiv> p div gcd p (pderiv p)"
  shows "sturm_seq (sturm_squarefree p) p'"
proof
  have "rsquarefree p'"
  proof (subst rsquarefree_roots, clarify)
    fix x assume "poly p' x = 0" "poly (pderiv p') x = 0"
    hence "[:-x,1:] dvd gcd p' (pderiv p')" by (simp add: poly_eq_0_iff_dvd)
    also from poly_div_gcd_squarefree(1)[OF assms(1)]
        have "gcd p' (pderiv p') = 1" by simp
    finally show False by (simp add: poly_eq_0_iff_dvd[symmetric])
  qed

  from sturm_seq_sturm[OF `rsquarefree p'`]
      interpret sturm_seq: sturm_seq "sturm_squarefree p" p'
      by (simp add: sturm_squarefree_def)

  show "\<And>x y. sgn (poly (last (sturm_squarefree p)) x) =
      sgn (poly (last (sturm_squarefree p)) y)" by simp
  show "sturm_squarefree p \<noteq> []" by simp
  show "hd (sturm_squarefree p) = p'" by (simp add: sturm_squarefree_def)
  show "length (sturm_squarefree p) \<ge> 2" by simp

  have [simp]: "sturm_squarefree p ! 0 = p'"
               "sturm_squarefree p ! Suc 0 = pderiv p'"
      by (simp_all add: sturm_squarefree_def)

  from `rsquarefree p'`
      show "\<And>x. \<not> (poly p' x = 0 \<and> poly (sturm_squarefree p ! 1) x = 0)"
      by (simp add: rsquarefree_roots)

  from sturm_seq.signs show "\<And>i x. \<lbrakk>i < length (sturm_squarefree p) - 2;
                                 poly (sturm_squarefree p ! (i + 1)) x = 0\<rbrakk>
                                 \<Longrightarrow> poly (sturm_squarefree p ! (i + 2)) x *
                                         poly (sturm_squarefree p ! i) x < 0" .

  from sturm_seq.deriv show "\<And>x\<^sub>0. poly p' x\<^sub>0 = 0 \<Longrightarrow>
         eventually (\<lambda>x. sgn (poly (p' * sturm_squarefree p ! 1) x) =
                         (if x > x\<^sub>0 then 1 else -1)) (at x\<^sub>0)" .
qed


subsubsection {* Optimisation for multiple roots *}

text {*
  We can also define the following non-canonical Sturm sequence that
  is obtained by taking the canonical Sturm sequence of $p$
  (possibly with multiple roots) and then dividing the entire
  sequence by the GCD of $p$ and its derivative.
*}
definition sturm_squarefree' where
"sturm_squarefree' p = (let d = gcd p (pderiv p)
                         in map (\<lambda>p'. p' div d) (sturm p))"

text {*
  This construction also has all the desired properties:
*}

lemma sturm_squarefree'_adjacent_root_propagate_left:
  assumes "p \<noteq> 0"
  assumes "i < length (sturm_squarefree' (p :: real poly)) - 1"
  assumes "poly (sturm_squarefree' p ! i) x = 0"
      and "poly (sturm_squarefree' p ! (i + 1)) x = 0"
  shows "\<forall>j\<le>i+1. poly (sturm_squarefree' p ! j) x = 0"
proof (intro sturm_adjacent_root_aux[OF assms(2,3,4)], goal_cases)
  case prems: (1 i x)
    def q \<equiv> "sturm p ! i"
    def r \<equiv> "sturm p ! (Suc i)"
    def s \<equiv> "sturm p ! (Suc (Suc i))"
    def d \<equiv> "gcd p (pderiv p)"
    def q' \<equiv> "q div d" and r' \<equiv> "r div d" and s' \<equiv> "s div d"
    from `p \<noteq> 0` have "d \<noteq> 0" unfolding d_def by simp
    from prems(1) have i_in_range: "i < length (sturm p) - 2"
        unfolding sturm_squarefree'_def Let_def by simp
    have [simp]: "d dvd q" "d dvd r" "d dvd s" unfolding q_def r_def s_def d_def
        using i_in_range by (auto intro: sturm_gcd)
    hence qrs_simps: "q = q' * d" "r = r' * d" "s = s' * d"
        unfolding q'_def r'_def s'_def by (simp_all)
    with prems(2) i_in_range have r'_0: "poly r' x = 0"
        unfolding r'_def r_def d_def sturm_squarefree'_def Let_def by simp
    hence r_0: "poly r x = 0" by (simp add: `r = r' * d`)
    from sturm_indices[OF i_in_range] have "q = q div r * r - s"
        unfolding q_def r_def s_def by (simp add: mod_div_equality)
    hence "q' = (q div r * r - s) div d" by (simp add: q'_def)
    also have "... = (q div r * r) div d - s'"
        unfolding s'_def by (simp)
    also have "... = q div r * r' - s'"
        using dvd_div_mult[OF `d dvd r`, of "q div r"]
        by (simp add: algebra_simps r'_def)
    also have "q div r = q' div r'" by (simp add: qrs_simps `d \<noteq> 0`)
    finally have "poly q' x = poly (q' div r' * r' - s') x" by simp
    also from r'_0 have "... = -poly s' x" by simp
    finally have "poly s' x = -poly q' x" by simp
    thus ?case using i_in_range
        unfolding q'_def s'_def q_def s_def sturm_squarefree'_def Let_def
        by (simp add: d_def sgn_minus)
qed

lemma sturm_squarefree'_adjacent_roots:
  assumes "p \<noteq> 0"
           "i < length (sturm_squarefree' (p :: real poly)) - 1"
          "poly (sturm_squarefree' p ! i) x = 0"
          "poly (sturm_squarefree' p ! (i + 1)) x = 0"
  shows False
proof-
  def d \<equiv> "gcd p (pderiv p)"
  from sturm_squarefree'_adjacent_root_propagate_left[OF assms]
      have "poly (sturm_squarefree' p ! 0) x = 0"
           "poly (sturm_squarefree' p ! 1) x = 0" by auto
  hence "poly (p div d) x = 0" "poly (pderiv p div d) x = 0"
      using assms(2)
      unfolding sturm_squarefree'_def Let_def d_def by auto
  moreover from div_gcd_coprime_poly assms(1)
      have "coprime (p div d) (pderiv p div d)" unfolding d_def by auto
  ultimately show False using coprime_imp_no_common_roots by auto
qed

lemma sturm_squarefree'_signs:
  assumes "p \<noteq> 0"
  assumes i_in_range: "i < length (sturm_squarefree' (p :: real poly)) - 2"
  assumes q_0: "poly (sturm_squarefree' p ! (i+1)) x = 0" (is "poly ?q x = 0")
  shows "poly (sturm_squarefree' p ! (i+2)) x *
         poly (sturm_squarefree' p ! i) x < 0"
            (is "poly ?r x * poly ?p x < 0")
proof-
  def d \<equiv> "gcd p (pderiv p)"
  with `p \<noteq> 0` have [simp]: "d \<noteq> 0" by simp
  from poly_div_gcd_squarefree(1)[OF `p \<noteq> 0`]
       coprime_imp_no_common_roots
      have rsquarefree: "rsquarefree (p div d)"
      by (auto simp: rsquarefree_roots d_def)

  from i_in_range have i_in_range': "i < length (sturm p) - 2"
      unfolding sturm_squarefree'_def by simp
  hence "d dvd (sturm p ! i)" (is "d dvd ?p'")
        "d dvd (sturm p ! (Suc i))" (is "d dvd ?q'")
        "d dvd (sturm p ! (Suc (Suc i)))" (is "d dvd ?r'")
      unfolding d_def by (auto intro: sturm_gcd)
  hence pqr_simps: "?p' = ?p * d" "?q' = ?q * d" "?r' = ?r * d"
    unfolding sturm_squarefree'_def Let_def d_def using i_in_range'
    by (auto simp: dvd_div_mult_self)
  with q_0 have q'_0: "poly ?q' x = 0" by simp
  from sturm_indices[OF i_in_range']
      have "sturm p ! (i+2) = - (sturm p ! i mod sturm p ! (i+1))" .
  hence "-?r' = ?p' mod ?q'" by simp
  with mod_div_equality[of ?p' ?q'] have "?p' div ?q' * ?q' - ?r' = ?p'" by simp
  hence "d*(?p div ?q * ?q - ?r) = d* ?p" by (simp add: pqr_simps algebra_simps)
  hence "?p div ?q * ?q - ?r = ?p" by simp
  hence "poly (?p div ?q) x * poly ?q x - poly ?r x = poly ?p x"
      by (metis poly_diff poly_mult)
  with q_0 have r_x: "poly ?r x = -poly ?p x" by simp

  from sturm_squarefree'_adjacent_roots[OF `p \<noteq> 0`] i_in_range q_0
      have "poly ?p x \<noteq> 0" by force
  moreover have sqr_pos: "\<And>x::real. x \<noteq> 0 \<Longrightarrow> x * x > 0" apply (case_tac "x \<ge> 0")
      by (simp_all add: mult_neg_neg)
  ultimately show ?thesis using r_x by simp
qed


text {*
  This approach indeed also yields a valid squarefree Sturm sequence
  for the polynomial $p/\text{gcd}(p,p')$.
*}
lemma sturm_seq_sturm_squarefree':
  assumes "(p :: real poly) \<noteq> 0"
  defines "d \<equiv> gcd p (pderiv p)"
  shows "sturm_seq (sturm_squarefree' p) (p div d)"
      (is "sturm_seq ?ps' ?p'")
proof
  show "?ps' \<noteq> []" "hd ?ps' = ?p'" "2 \<le> length ?ps'"
      by (simp_all add: sturm_squarefree'_def d_def hd_map)

  from assms have "d \<noteq> 0" by simp
  {
    have "d dvd last (sturm p)" unfolding d_def
        by (rule sturm_gcd, simp)
    hence "last (sturm p) = last ?ps' * d"
        by (simp add: sturm_squarefree'_def last_map d_def dvd_div_mult_self)
    moreover from this have "last ?ps' dvd last (sturm p)" by simp
    moreover note dvd_imp_degree_le[OF this]
    ultimately have "degree (last ?ps') \<le> degree (last (sturm p))"
        using `d \<noteq> 0` by (cases "last ?ps' = 0", auto)
    hence "degree (last ?ps') = 0" by simp
    then obtain c where "last ?ps' = [:c:]"
        by (cases "last ?ps'", simp split: split_if_asm)
    thus "\<And>x y. sgn (poly (last ?ps') x) = sgn (poly (last ?ps') y)" by simp
  }

  have squarefree: "rsquarefree ?p'" using `p \<noteq> 0`
    by (subst rsquarefree_roots, unfold d_def,
        intro allI coprime_imp_no_common_roots poly_div_gcd_squarefree)
  have [simp]: "sturm_squarefree' p ! Suc 0 = pderiv p div d"
      unfolding sturm_squarefree'_def Let_def sturm_def d_def
          by (subst sturm_aux.simps, simp)
  have coprime: "coprime ?p' (pderiv p div d)"
      unfolding d_def using div_gcd_coprime_poly `p \<noteq> 0` by blast
  thus squarefree':
      "\<And>x. \<not> (poly (p div d) x = 0 \<and> poly (sturm_squarefree' p ! 1) x = 0)"
      using coprime_imp_no_common_roots by simp

  from sturm_squarefree'_signs[OF `p \<noteq> 0`]
      show "\<And>i x. \<lbrakk>i < length ?ps' - 2; poly (?ps' ! (i + 1)) x = 0\<rbrakk>
                \<Longrightarrow> poly (?ps' ! (i + 2)) x * poly (?ps' ! i) x < 0" .

  have [simp]: "?p' \<noteq> 0" using squarefree by (simp add: rsquarefree_def)
  have A: "?p' = ?ps' ! 0" "pderiv p div d = ?ps' ! 1"
      by (simp_all add: sturm_squarefree'_def Let_def d_def sturm_def,
          subst sturm_aux.simps, simp)
  have [simp]: "?ps' ! 0 \<noteq> 0" using squarefree
      by (auto simp: A rsquarefree_def)

  fix x\<^sub>0 :: real
  assume "poly ?p' x\<^sub>0 = 0"
  hence "poly p x\<^sub>0 = 0" using poly_div_gcd_squarefree(2)[OF `p \<noteq> 0`]
      unfolding d_def by simp
  hence "pderiv p \<noteq> 0" using `p \<noteq> 0` by (auto dest: pderiv_iszero)
  with `p \<noteq> 0` `poly p x\<^sub>0 = 0`
      have A: "eventually (\<lambda>x. sgn (poly (p * pderiv p) x) =
                              (if x\<^sub>0 < x then 1 else -1)) (at x\<^sub>0)"
      by (intro sturm_firsttwo_signs_aux, simp_all)
  note ev = eventually_conj[OF A poly_neighbourhood_without_roots[OF `d \<noteq> 0`]]

  show "eventually (\<lambda>x. sgn (poly (p div d * sturm_squarefree' p ! 1) x) =
                        (if x\<^sub>0 < x then 1 else -1)) (at x\<^sub>0)"
  proof (rule eventually_mono[OF ev], goal_cases)
      have [intro]:
          "\<And>a (b::real). b \<noteq> 0 \<Longrightarrow> a < 0 \<Longrightarrow> a / (b * b) < 0"
          "\<And>a (b::real). b \<noteq> 0 \<Longrightarrow> a > 0 \<Longrightarrow> a / (b * b) > 0"
          by ((case_tac "b > 0",
              auto simp: mult_neg_neg field_simps) [])+
    case prems: (1 x)
      hence  [simp]: "poly d x * poly d x > 0"
           by (cases "poly d x > 0", auto simp: mult_neg_neg)
      from poly_div_gcd_squarefree_aux(2)[OF `pderiv p \<noteq> 0`]
          have "poly (p div d) x = 0 \<longleftrightarrow> poly p x = 0" by (simp add: d_def)
      moreover have "d dvd p" "d dvd pderiv p" unfolding d_def by simp_all
      ultimately show ?case using prems
          by (auto simp: sgn_real_def poly_div not_less[symmetric]
                         zero_less_divide_iff split: split_if_asm)
  qed
qed


text {*
  This construction is obviously more expensive to compute than the one that \emph{first}
  divides $p$ by $\text{gcd}(p,p')$ and \emph{then} applies the canonical construction.
  In this construction, we \emph{first} compute the canonical Sturm sequence of $p$ as if
  it had no multiple roots and \emph{then} divide by the GCD.
  However, it can be seen quite easily that unless $x$ is a multiple root of $p$,
  i.\,e. as long as $\text{gcd}(P,P')\neq 0$, the number of sign changes in a sequence of
  polynomials does not actually change when we divide the polynomials by $\text{gcd}(p,p')$.\\
  There\-fore we can use the ca\-no\-ni\-cal Sturm se\-quence even in the non-square\-free
  case as long as the borders of the interval we are interested in are not multiple roots
  of the polynomial.
*}

lemma sign_changes_mult_aux:
  assumes "d \<noteq> (0::real)"
  shows "length (remdups_adj (filter (\<lambda>x. x \<noteq> 0) (map (op *d \<circ> f) xs))) =
         length (remdups_adj (filter (\<lambda>x. x \<noteq> 0) (map f xs)))"
proof-
  from assms have inj: "inj (op *d)" by (auto intro: injI)
  from assms have [simp]: "filter (\<lambda>x. (op* d \<circ> f) x \<noteq> 0) = filter (\<lambda>x. f x \<noteq> 0)"
                          "filter ((\<lambda>x. x \<noteq> 0) \<circ> f) = filter (\<lambda>x. f x \<noteq> 0)"
      by (simp_all add: o_def)
  have "filter (\<lambda>x. x \<noteq> 0) (map (op* d \<circ> f) xs) =
        map (op* d \<circ> f) (filter (\<lambda>x. (op* d \<circ> f) x \<noteq> 0) xs)"
      by (simp add: filter_map o_def)
  thus ?thesis using remdups_adj_map_injective[OF inj] assms
      by (simp add: filter_map map_map[symmetric] del: map_map)
qed

lemma sturm_sturm_squarefree'_same_sign_changes:
  fixes p :: "real poly"
  defines "ps \<equiv> sturm p" and "ps' \<equiv> sturm_squarefree' p"
  shows "poly p x \<noteq> 0 \<or> poly (pderiv p) x \<noteq> 0 \<Longrightarrow>
             sign_changes ps' x = sign_changes ps x"
        "p \<noteq> 0 \<Longrightarrow> sign_changes_inf ps' = sign_changes_inf ps"
        "p \<noteq> 0 \<Longrightarrow> sign_changes_neg_inf ps' = sign_changes_neg_inf ps"
proof-
  def d \<equiv> "gcd p (pderiv p)"
  def p' \<equiv> "p div d"
  def s' \<equiv> "poly_inf d"
  def s'' \<equiv> "poly_neg_inf d"

  {
    fix x :: real and q :: "real poly"
    assume "q \<in> set ps"
    hence "d dvd q" unfolding d_def ps_def using sturm_gcd by simp
    hence q_prod: "q = (q div d) * d" unfolding p'_def d_def
        by (simp add: algebra_simps dvd_mult_div_cancel)

    have "poly q x = poly d x * poly (q div d) x"  by (subst q_prod, simp)
    hence s1: "sgn (poly q x) = sgn (poly d x) * sgn (poly (q div d) x)"
        by (subst q_prod, simp add: sgn_mult)
    from poly_inf_mult have s2: "poly_inf q = s' * poly_inf (q div d)"
        unfolding s'_def by (subst q_prod, simp)
    from poly_inf_mult have s3: "poly_neg_inf q = s'' * poly_neg_inf (q div d)"
        unfolding s''_def by (subst q_prod, simp)
    note s1 s2 s3
  }
  note signs = this

  {
    fix f :: "real poly \<Rightarrow> real" and s :: real
    assume f: "\<And>q. q \<in> set ps \<Longrightarrow> f q = s * f (q div d)" and s: "s \<noteq> 0"
    hence "inverse s \<noteq> 0" by simp
    {fix q assume "q \<in> set ps"
     hence "f (q div d) = inverse s * f q"
         by (subst f[of q], simp_all add: s)
    } note f' = this
    have "length (remdups_adj [x\<leftarrow>map f (map (\<lambda>q. q div d) ps). x \<noteq> 0]) - 1 =
           length (remdups_adj [x\<leftarrow>map (\<lambda>q. f (q div d)) ps . x \<noteq> 0]) - 1"
        by (simp only: sign_changes_def o_def map_map)
    also have "map (\<lambda>q. q div d) ps = ps'"
        by (simp add: ps_def ps'_def sturm_squarefree'_def Let_def d_def)
    also from f' have "map (\<lambda>q. f (q div d)) ps =
                      map (\<lambda>x. (op*(inverse s) \<circ> f) x) ps" by (simp add: o_def)
    also note sign_changes_mult_aux[OF `inverse s \<noteq> 0`, of f ps]
    finally have
        "length (remdups_adj [x\<leftarrow>map f ps' . x \<noteq> 0]) - 1 =
         length (remdups_adj [x\<leftarrow>map f ps . x \<noteq> 0]) - 1" by simp
  }
  note length_remdups_adj = this

  {
    fix x assume A: "poly p x \<noteq> 0 \<or> poly (pderiv p) x \<noteq> 0"
    have "d dvd p" "d dvd pderiv p" unfolding d_def by simp_all
    with A have "sgn (poly d x) \<noteq> 0"
        by (auto simp add: sgn_zero_iff elim: dvdE)
    thus "sign_changes ps' x = sign_changes ps x" using signs(1)
        unfolding sign_changes_def
        by (intro length_remdups_adj[of "\<lambda>q. sgn (poly q x)"], simp_all)
  }

  assume "p \<noteq> 0"
  hence "d \<noteq> 0" unfolding d_def by simp
  hence "s' \<noteq> 0" "s'' \<noteq> 0" unfolding s'_def s''_def by simp_all
  from length_remdups_adj[of poly_inf s', OF signs(2) `s' \<noteq> 0`]
      show "sign_changes_inf ps' = sign_changes_inf ps"
      unfolding sign_changes_inf_def .
  from length_remdups_adj[of poly_neg_inf s'', OF signs(3) `s'' \<noteq> 0`]
      show "sign_changes_neg_inf ps' = sign_changes_neg_inf ps"
      unfolding sign_changes_neg_inf_def .
qed



subsection {* Root-counting functions *}

text {*
  With all these results, we can now define functions that count roots
  in bounded and unbounded intervals:
*}

definition count_roots_between where
"count_roots_between p a b = (if a \<le> b \<and> p \<noteq> 0 then
  (let ps = sturm_squarefree p
    in sign_changes ps a - sign_changes ps b) else 0)"

definition count_roots where
"count_roots p = (if (p::real poly) = 0 then 0 else
  (let ps = sturm_squarefree p
    in sign_changes_neg_inf ps - sign_changes_inf ps))"

definition count_roots_above where
"count_roots_above p a = (if (p::real poly) = 0 then 0 else
  (let ps = sturm_squarefree p
    in sign_changes ps a - sign_changes_inf ps))"

definition count_roots_below where
"count_roots_below p a = (if (p::real poly) = 0 then 0 else
  (let ps = sturm_squarefree p
    in sign_changes_neg_inf ps - sign_changes ps a))"


lemma count_roots_between_correct:
  "count_roots_between p a b = card {x. a < x \<and> x \<le> b \<and> poly p x = 0}"
proof (cases "p \<noteq> 0 \<and> a \<le> b")
  case False
    note False' = this
    hence "card {x. a < x \<and> x \<le> b \<and> poly p x = 0} = 0"
    proof (cases "a < b")
      case True
        with False have [simp]: "p = 0" by simp
        have subset: "{a<..<b} \<subseteq> {x. a < x \<and> x \<le> b \<and> poly p x = 0}" by auto
        from infinite_Ioo[OF True] have "\<not>finite {a<..<b}" .
        hence "\<not>finite {x. a < x \<and> x \<le> b \<and> poly p x = 0}"
            using finite_subset[OF subset] by blast
        thus ?thesis by simp
    next
      case False
        with False' show ?thesis by (auto simp: not_less card_eq_0_iff)
    qed
    thus ?thesis unfolding count_roots_between_def Let_def using False by auto
next
  case True
  hence "p \<noteq> 0" "a \<le> b" by simp_all
  def p' \<equiv> "p div (gcd p (pderiv p))"
  from poly_div_gcd_squarefree(1)[OF `p \<noteq> 0`] have "p' \<noteq> 0"
      unfolding p'_def by clarsimp

  from sturm_seq_sturm_squarefree[OF `p \<noteq> 0`]
      interpret sturm_seq "sturm_squarefree p" p'
      unfolding p'_def .
  from poly_roots_finite[OF `p' \<noteq> 0`]
      have "finite {x. a < x \<and> x \<le> b \<and> poly p' x = 0}" by fast
  have "count_roots_between p a b = card {x. a < x \<and> x \<le> b \<and> poly p' x = 0}"
      unfolding count_roots_between_def Let_def
      using True count_roots_between[OF `p' \<noteq> 0` `a \<le> b`] by simp
  also from poly_div_gcd_squarefree(2)[OF `p \<noteq> 0`]
      have "{x. a < x \<and> x \<le> b \<and> poly p' x = 0} =
            {x. a < x \<and> x \<le> b \<and> poly p x = 0}" unfolding p'_def by blast
  finally show ?thesis .
qed

lemma count_roots_correct:
  fixes p :: "real poly"
  shows "count_roots p = card {x. poly p x = 0}" (is "_ = card ?S")
proof (cases "p = 0")
  case True
    with infinite_Ioo[of 0 1] finite_subset[of "{0<..<1}" ?S]
        have "\<not>finite {x. poly p x = 0}" by force
    thus ?thesis by (simp add: count_roots_def True)
next
  case False
  def p' \<equiv> "p div (gcd p (pderiv p))"
  from poly_div_gcd_squarefree(1)[OF `p \<noteq> 0`] have "p' \<noteq> 0"
      unfolding p'_def by clarsimp

  from sturm_seq_sturm_squarefree[OF `p \<noteq> 0`]
      interpret sturm_seq "sturm_squarefree p" p'
      unfolding p'_def .
  from count_roots[OF `p' \<noteq> 0`]
      have "count_roots p = card {x. poly p' x = 0}"
      unfolding count_roots_def Let_def by (simp add: `p \<noteq> 0`)
  also from poly_div_gcd_squarefree(2)[OF `p \<noteq> 0`]
      have "{x. poly p' x = 0} = {x. poly p x = 0}" unfolding p'_def by blast
  finally show ?thesis .
qed

lemma count_roots_above_correct:
  fixes p :: "real poly"
  shows "count_roots_above p a = card {x. x > a \<and> poly p x = 0}"
         (is "_ = card ?S")
proof (cases "p = 0")
  case True
    with infinite_Ioo[of a "a+1"] finite_subset[of "{a<..<a+1}" ?S]
        have "\<not>finite {x. x > a \<and> poly p x = 0}" by force
    thus ?thesis by (simp add: count_roots_above_def True)
next
  case False
  def p' \<equiv> "p div (gcd p (pderiv p))"
  from poly_div_gcd_squarefree(1)[OF `p \<noteq> 0`] have "p' \<noteq> 0"
      unfolding p'_def by clarsimp

  from sturm_seq_sturm_squarefree[OF `p \<noteq> 0`]
      interpret sturm_seq "sturm_squarefree p" p'
      unfolding p'_def .
  from count_roots_above[OF `p' \<noteq> 0`]
      have "count_roots_above p a = card {x. x > a \<and> poly p' x = 0}"
      unfolding count_roots_above_def Let_def by (simp add: `p \<noteq> 0`)
  also from poly_div_gcd_squarefree(2)[OF `p \<noteq> 0`]
      have "{x. x > a \<and> poly p' x = 0} = {x. x > a \<and> poly p x = 0}"
      unfolding p'_def by blast
  finally show ?thesis .
qed

lemma count_roots_below_correct:
  fixes p :: "real poly"
  shows "count_roots_below p a = card {x. x \<le> a \<and> poly p x = 0}"
         (is "_ = card ?S")
proof (cases "p = 0")
  case True
    with infinite_Ioo[of "a - 1" a]
         finite_subset[of "{a - 1<..<a}" ?S]
        have "\<not>finite {x. x \<le> a \<and> poly p x = 0}" by force
    thus ?thesis by (simp add: count_roots_below_def True)
next
  case False
  def p' \<equiv> "p div (gcd p (pderiv p))"
  from poly_div_gcd_squarefree(1)[OF `p \<noteq> 0`] have "p' \<noteq> 0"
      unfolding p'_def by clarsimp

  from sturm_seq_sturm_squarefree[OF `p \<noteq> 0`]
      interpret sturm_seq "sturm_squarefree p" p'
      unfolding p'_def .
  from count_roots_below[OF `p' \<noteq> 0`]
      have "count_roots_below p a = card {x. x \<le> a \<and> poly p' x = 0}"
      unfolding count_roots_below_def Let_def by (simp add: `p \<noteq> 0`)
  also from poly_div_gcd_squarefree(2)[OF `p \<noteq> 0`]
      have "{x. x \<le> a \<and> poly p' x = 0} = {x. x \<le> a \<and> poly p x = 0}"
      unfolding p'_def by blast
  finally show ?thesis .
qed

text {*
  The optimisation explained above can be used to prove more efficient code equations that
  use the more efficient construction in the case that the interval borders are not
  multiple roots:
*}

lemma count_roots_between[code]:
  "count_roots_between p a b =
     (let q = pderiv p
       in if a > b \<or> p = 0 then 0
       else if (poly p a \<noteq> 0 \<or> poly q a \<noteq> 0) \<and> (poly p b \<noteq> 0 \<or> poly q b \<noteq> 0)
            then (let ps = sturm p
                   in sign_changes ps a - sign_changes ps b)
            else (let ps = sturm_squarefree p
                   in sign_changes ps a - sign_changes ps b))"
proof (cases "a > b \<or> p = 0")
  case True
    thus ?thesis by (auto simp add: count_roots_between_def Let_def)
next
  case False
    note False1 = this
    hence "a \<le> b" "p \<noteq> 0" by simp_all
    thus ?thesis
    proof (cases "(poly p a \<noteq> 0 \<or> poly (pderiv p) a \<noteq> 0) \<and>
                  (poly p b \<noteq> 0 \<or> poly (pderiv p) b \<noteq> 0)")
    case False
      thus ?thesis using False1
          by (auto simp add: Let_def count_roots_between_def)
    next
    case True
      hence A: "poly p a \<noteq> 0 \<or> poly (pderiv p) a \<noteq> 0" and
            B: "poly p b \<noteq> 0 \<or> poly (pderiv p) b \<noteq> 0" by auto
      def d \<equiv> "gcd p (pderiv p)"
      from `p \<noteq> 0` have [simp]: "p div d \<noteq> 0"
          using poly_div_gcd_squarefree(1)[OF `p \<noteq> 0`] by (auto simp add: d_def)
      from sturm_seq_sturm_squarefree'[OF `p \<noteq> 0`]
          interpret sturm_seq "sturm_squarefree' p" "p div d"
          unfolding sturm_squarefree'_def Let_def d_def .
      note count_roots_between_correct
      also have "{x. a < x \<and> x \<le> b \<and> poly p x = 0} =
                 {x. a < x \<and> x \<le> b \<and> poly (p div d) x = 0}"
          unfolding d_def using poly_div_gcd_squarefree(2)[OF `p \<noteq> 0`] by simp
      also note count_roots_between[OF `p div d \<noteq> 0` `a \<le> b`, symmetric]
      also note sturm_sturm_squarefree'_same_sign_changes(1)[OF A]
      also note sturm_sturm_squarefree'_same_sign_changes(1)[OF B]
      finally show ?thesis using True False by (simp add: Let_def)
    qed
qed


lemma count_roots_code[code]:
  "count_roots (p::real poly) =
    (if p = 0 then 0
     else let ps = sturm p
           in sign_changes_neg_inf ps - sign_changes_inf ps)"
proof (cases "p = 0", simp add: count_roots_def)
  case False
    def d \<equiv> "gcd p (pderiv p)"
    from `p \<noteq> 0` have [simp]: "p div d \<noteq> 0"
        using poly_div_gcd_squarefree(1)[OF `p \<noteq> 0`] by (auto simp add: d_def)
    from sturm_seq_sturm_squarefree'[OF `p \<noteq> 0`]
        interpret sturm_seq "sturm_squarefree' p" "p div d"
        unfolding sturm_squarefree'_def Let_def d_def .

    note count_roots_correct
    also have "{x. poly p x = 0} = {x. poly (p div d) x = 0}"
        unfolding d_def using poly_div_gcd_squarefree(2)[OF `p \<noteq> 0`] by simp
    also note count_roots[OF `p div d \<noteq> 0`, symmetric]
    also note sturm_sturm_squarefree'_same_sign_changes(2)[OF `p \<noteq> 0`]
    also note sturm_sturm_squarefree'_same_sign_changes(3)[OF `p \<noteq> 0`]
    finally show ?thesis using False unfolding Let_def by simp
qed


lemma count_roots_above_code[code]:
  "count_roots_above p a =
     (let q = pderiv p
       in if p = 0 then 0
       else if poly p a \<noteq> 0 \<or> poly q a \<noteq> 0
            then (let ps = sturm p
                   in sign_changes ps a - sign_changes_inf ps)
            else (let ps = sturm_squarefree p
                   in sign_changes ps a - sign_changes_inf ps))"
proof (cases "p = 0")
  case True
    thus ?thesis by (auto simp add: count_roots_above_def Let_def)
next
  case False
    note False1 = this
    hence "p \<noteq> 0" by simp_all
    thus ?thesis
    proof (cases "(poly p a \<noteq> 0 \<or> poly (pderiv p) a \<noteq> 0)")
    case False
      thus ?thesis using False1
          by (auto simp add: Let_def count_roots_above_def)
    next
    case True
      hence A: "poly p a \<noteq> 0 \<or> poly (pderiv p) a \<noteq> 0" by simp
      def d \<equiv> "gcd p (pderiv p)"
      from `p \<noteq> 0` have [simp]: "p div d \<noteq> 0"
          using poly_div_gcd_squarefree(1)[OF `p \<noteq> 0`] by (auto simp add: d_def)
      from sturm_seq_sturm_squarefree'[OF `p \<noteq> 0`]
          interpret sturm_seq "sturm_squarefree' p" "p div d"
          unfolding sturm_squarefree'_def Let_def d_def .
      note count_roots_above_correct
      also have "{x. a < x \<and> poly p x = 0} =
                 {x. a < x \<and> poly (p div d) x = 0}"
          unfolding d_def using poly_div_gcd_squarefree(2)[OF `p \<noteq> 0`] by simp
      also note count_roots_above[OF `p div d \<noteq> 0`, symmetric]
      also note sturm_sturm_squarefree'_same_sign_changes(1)[OF A]
      also note sturm_sturm_squarefree'_same_sign_changes(2)[OF `p \<noteq> 0`]
      finally show ?thesis using True False by (simp add: Let_def)
    qed
qed

lemma count_roots_below_code[code]:
  "count_roots_below p a =
     (let q = pderiv p
       in if p = 0 then 0
       else if poly p a \<noteq> 0 \<or> poly q a \<noteq> 0
            then (let ps = sturm p
                   in sign_changes_neg_inf ps - sign_changes ps a)
            else (let ps = sturm_squarefree p
                   in sign_changes_neg_inf ps - sign_changes ps a))"
proof (cases "p = 0")
  case True
    thus ?thesis by (auto simp add: count_roots_below_def Let_def)
next
  case False
    note False1 = this
    hence "p \<noteq> 0" by simp_all
    thus ?thesis
    proof (cases "(poly p a \<noteq> 0 \<or> poly (pderiv p) a \<noteq> 0)")
    case False
      thus ?thesis using False1
          by (auto simp add: Let_def count_roots_below_def)
    next
    case True
      hence A: "poly p a \<noteq> 0 \<or> poly (pderiv p) a \<noteq> 0" by simp
      def d \<equiv> "gcd p (pderiv p)"
      from `p \<noteq> 0` have [simp]: "p div d \<noteq> 0"
          using poly_div_gcd_squarefree(1)[OF `p \<noteq> 0`] by (auto simp add: d_def)
      from sturm_seq_sturm_squarefree'[OF `p \<noteq> 0`]
          interpret sturm_seq "sturm_squarefree' p" "p div d"
          unfolding sturm_squarefree'_def Let_def d_def .
      note count_roots_below_correct
      also have "{x. x \<le> a \<and> poly p x = 0} =
                 {x. x \<le> a \<and> poly (p div d) x = 0}"
          unfolding d_def using poly_div_gcd_squarefree(2)[OF `p \<noteq> 0`] by simp
      also note count_roots_below[OF `p div d \<noteq> 0`, symmetric]
      also note sturm_sturm_squarefree'_same_sign_changes(1)[OF A]
      also note sturm_sturm_squarefree'_same_sign_changes(3)[OF `p \<noteq> 0`]
      finally show ?thesis using True False by (simp add: Let_def)
    qed
qed

end
