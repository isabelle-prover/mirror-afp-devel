(*  Title:      ZF/Constructible/Datatype_absolute.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

section \<open>Absoluteness Properties for Recursive Datatypes\<close>

theory Datatype_absolute imports Eclose_Absolute begin

locale M_datatypes = M_trancl +
 assumes list_replacement1:
   "M(A) ==> iterates_replacement(M, is_list_functor(M,A), 0)"
  and list_replacement2:
   "M(A) ==> strong_replacement(M,
         \<lambda>n y. n\<in>nat & is_iterates(M, is_list_functor(M,A), 0, n, y))"
  and formula_replacement1:
   "iterates_replacement(M, is_formula_functor(M), 0)"
  and formula_replacement2:
   "strong_replacement(M,
         \<lambda>n y. n\<in>nat & is_iterates(M, is_formula_functor(M), 0, n, y))"
  and nth_replacement:
   "M(l) ==> iterates_replacement(M, %l t. is_tl(M,l,t), l)"


subsubsection\<open>Absoluteness of the List Construction\<close>

lemma (in M_datatypes) list_replacement2':
  "M(A) ==> strong_replacement(M, \<lambda>n y. n\<in>nat & y = (\<lambda>X. {0} + A * X)^n (0))"
apply (insert list_replacement2 [of A])
apply (rule strong_replacement_cong [THEN iffD1])
apply (rule conj_cong [OF iff_refl iterates_abs [of "is_list_functor(M,A)"]])
apply (simp_all add: list_replacement1 relation1_def)
done

lemma (in M_datatypes) list_closed [intro,simp]:
     "M(A) ==> M(list(A))"
apply (insert list_replacement1)
by  (simp add: RepFun_closed2 list_eq_Union
               list_replacement2' relation1_def
               iterates_closed [of "is_list_functor(M,A)"])

text\<open>WARNING: use only with \<open>dest:\<close> or with variables fixed!\<close>
lemmas (in M_datatypes) list_into_M = transM [OF _ list_closed]

lemma (in M_datatypes) list_N_abs [simp]:
     "[|M(A); n\<in>nat; M(Z)|]
      ==> is_list_N(M,A,n,Z) \<longleftrightarrow> Z = list_N(A,n)"
apply (insert list_replacement1)
apply (simp add: is_list_N_def list_N_def relation1_def nat_into_M
                 iterates_abs [of "is_list_functor(M,A)" _ "\<lambda>X. {0} + A*X"])
done

lemma (in M_datatypes) list_N_closed [intro,simp]:
     "[|M(A); n\<in>nat|] ==> M(list_N(A,n))"
apply (insert list_replacement1)
apply (simp add: is_list_N_def list_N_def relation1_def nat_into_M
                 iterates_closed [of "is_list_functor(M,A)"])
done

lemma (in M_datatypes) mem_list_abs [simp]:
     "M(A) ==> mem_list(M,A,l) \<longleftrightarrow> l \<in> list(A)"
apply (insert list_replacement1)
apply (simp add: mem_list_def list_N_def relation1_def list_eq_Union
                 iterates_closed [of "is_list_functor(M,A)"])
done

lemma (in M_datatypes) list_abs [simp]:
     "[|M(A); M(Z)|] ==> is_list(M,A,Z) \<longleftrightarrow> Z = list(A)"
apply (simp add: is_list_def, safe)
apply (rule M_equalityI, simp_all)
done

subsubsection\<open>Absoluteness of Formulas\<close>

lemma (in M_datatypes) formula_replacement2':
  "strong_replacement(M, \<lambda>n y. n\<in>nat & y = (\<lambda>X. ((nat*nat) + (nat*nat)) + (X*X + X))^n (0))"
apply (insert formula_replacement2)
apply (rule strong_replacement_cong [THEN iffD1])
apply (rule conj_cong [OF iff_refl iterates_abs [of "is_formula_functor(M)"]])
apply (simp_all add: formula_replacement1 relation1_def)
done

lemma (in M_datatypes) formula_closed [intro,simp]:
     "M(formula)"
apply (insert formula_replacement1)
apply  (simp add: RepFun_closed2 formula_eq_Union
                  formula_replacement2' relation1_def
                  iterates_closed [of "is_formula_functor(M)"])
done

lemmas (in M_datatypes) formula_into_M = transM [OF _ formula_closed]

lemma (in M_datatypes) formula_N_abs [simp]:
     "[|n\<in>nat; M(Z)|]
      ==> is_formula_N(M,n,Z) \<longleftrightarrow> Z = formula_N(n)"
apply (insert formula_replacement1)
apply (simp add: is_formula_N_def formula_N_def relation1_def nat_into_M
                 iterates_abs [of "is_formula_functor(M)" _
                                  "\<lambda>X. ((nat*nat) + (nat*nat)) + (X*X + X)"])
done

lemma (in M_datatypes) formula_N_closed [intro,simp]:
     "n\<in>nat ==> M(formula_N(n))"
apply (insert formula_replacement1)
apply (simp add: is_formula_N_def formula_N_def relation1_def nat_into_M
                 iterates_closed [of "is_formula_functor(M)"])
done

lemma (in M_datatypes) mem_formula_abs [simp]:
     "mem_formula(M,l) \<longleftrightarrow> l \<in> formula"
apply (insert formula_replacement1)
apply (simp add: mem_formula_def relation1_def formula_eq_Union formula_N_def
                 iterates_closed [of "is_formula_functor(M)"])
done

lemma (in M_datatypes) formula_abs [simp]:
     "[|M(Z)|] ==> is_formula(M,Z) \<longleftrightarrow> Z = formula"
apply (simp add: is_formula_def, safe)
apply (rule M_equalityI, simp_all)
done



lemma (in M_datatypes) length_abs [simp]:
     "[|M(A); l \<in> list(A); n \<in> nat|] ==> is_length(M,A,l,n) \<longleftrightarrow> n = length(l)"
apply (subgoal_tac "M(l) & M(n)")
 prefer 2 apply (blast dest: transM)
apply (simp add: is_length_def)
apply (blast intro: list_imp_list_N nat_into_Ord list_N_imp_eq_length
             dest: list_N_imp_length_lt)
done



definition
  is_nth :: "[i=>o,i,i,i] => o" where
    "is_nth(M,n,l,Z) ==
      \<exists>X[M]. is_iterates(M, is_tl(M), l, n, X) & is_hd(M,X,Z)"

lemma (in M_datatypes) nth_abs [simp]:
     "[|M(A); n \<in> nat; l \<in> list(A); M(Z)|]
      ==> is_nth(M,n,l,Z) \<longleftrightarrow> Z = nth(n,l)"
apply (subgoal_tac "M(l)")
 prefer 2 apply (blast intro: transM)
apply (simp add: is_nth_def nth_eq_hd_iterates_tl nat_into_M
                 tl'_closed iterates_tl'_closed
                 iterates_abs [OF _ relation1_tl] nth_replacement)
done



lemma (in M_datatypes) depth_abs [simp]:
     "[|p \<in> formula; n \<in> nat|] ==> is_depth(M,p,n) \<longleftrightarrow> n = depth(p)"
apply (subgoal_tac "M(p) & M(n)")
 prefer 2 apply (blast dest: transM)
apply (simp add: is_depth_def)
apply (blast intro: formula_imp_formula_N nat_into_Ord formula_N_imp_eq_depth
             dest: formula_N_imp_depth_lt)
done


subsubsection\<open>\<^term>\<open>is_formula_case\<close>: relativization of \<^term>\<open>formula_case\<close>\<close>

definition
 is_formula_case ::
    "[i=>o, [i,i,i]=>o, [i,i,i]=>o, [i,i,i]=>o, [i,i]=>o, i, i] => o" where
  \<comment> \<open>no constraint on non-formulas\<close>
  "is_formula_case(M, is_a, is_b, is_c, is_d, p, z) ==
      (\<forall>x[M]. \<forall>y[M]. finite_ordinal(M,x) \<longrightarrow> finite_ordinal(M,y) \<longrightarrow>
                      is_Member(M,x,y,p) \<longrightarrow> is_a(x,y,z)) &
      (\<forall>x[M]. \<forall>y[M]. finite_ordinal(M,x) \<longrightarrow> finite_ordinal(M,y) \<longrightarrow>
                      is_Equal(M,x,y,p) \<longrightarrow> is_b(x,y,z)) &
      (\<forall>x[M]. \<forall>y[M]. mem_formula(M,x) \<longrightarrow> mem_formula(M,y) \<longrightarrow>
                     is_Nand(M,x,y,p) \<longrightarrow> is_c(x,y,z)) &
      (\<forall>x[M]. mem_formula(M,x) \<longrightarrow> is_Forall(M,x,p) \<longrightarrow> is_d(x,z))"

lemma (in M_datatypes) formula_case_abs [simp]:
     "[| Relation2(M,nat,nat,is_a,a); Relation2(M,nat,nat,is_b,b);
         Relation2(M,formula,formula,is_c,c); Relation1(M,formula,is_d,d);
         p \<in> formula; M(z) |]
      ==> is_formula_case(M,is_a,is_b,is_c,is_d,p,z) \<longleftrightarrow>
          z = formula_case(a,b,c,d,p)"
apply (simp add: formula_into_M is_formula_case_def)
apply (erule formula.cases)
   apply (simp_all add: Relation1_def Relation2_def)
done

lemma (in M_datatypes) formula_case_closed [intro,simp]:
  "[|p \<in> formula;
     \<forall>x[M]. \<forall>y[M]. x\<in>nat \<longrightarrow> y\<in>nat \<longrightarrow> M(a(x,y));
     \<forall>x[M]. \<forall>y[M]. x\<in>nat \<longrightarrow> y\<in>nat \<longrightarrow> M(b(x,y));
     \<forall>x[M]. \<forall>y[M]. x\<in>formula \<longrightarrow> y\<in>formula \<longrightarrow> M(c(x,y));
     \<forall>x[M]. x\<in>formula \<longrightarrow> M(d(x))|] ==> M(formula_case(a,b,c,d,p))"
by (erule formula.cases, simp_all)


subsubsection \<open>Absoluteness for \<^term>\<open>formula_rec\<close>: Final Results\<close>

definition
  is_formula_rec :: "[i=>o, [i,i,i]=>o, i, i] => o" where
    \<comment> \<open>predicate to relativize the functional \<^term>\<open>formula_rec\<close>\<close>
   "is_formula_rec(M,MH,p,z)  ==
      \<exists>dp[M]. \<exists>i[M]. \<exists>f[M]. finite_ordinal(M,dp) & is_depth(M,p,dp) &
             successor(M,dp,i) & fun_apply(M,f,p,z) & is_transrec(M,MH,i,f)"


text\<open>Sufficient conditions to relativize the instance of \<^term>\<open>formula_case\<close>
      in \<^term>\<open>formula_rec\<close>\<close>
lemma (in M_datatypes) Relation1_formula_rec_case:
     "[|Relation2(M, nat, nat, is_a, a);
        Relation2(M, nat, nat, is_b, b);
        Relation2 (M, formula, formula,
           is_c, \<lambda>u v. c(u, v, h`succ(depth(u))`u, h`succ(depth(v))`v));
        Relation1(M, formula,
           is_d, \<lambda>u. d(u, h ` succ(depth(u)) ` u));
        M(h) |]
      ==> Relation1(M, formula,
                         is_formula_case (M, is_a, is_b, is_c, is_d),
                         formula_rec_case(a, b, c, d, h))"
apply (simp (no_asm) add: formula_rec_case_def Relation1_def)
apply (simp)
done


text\<open>This locale packages the premises of the following theorems,
      which is the normal purpose of locales.  It doesn't accumulate
      constraints on the class \<^term>\<open>M\<close>, as in most of this development.\<close>
locale Formula_Rec = M_eclose + M_datatypes +
  fixes a and is_a and b and is_b and c and is_c and d and is_d and MH
  defines
      "MH(u::i,f,z) ==
        \<forall>fml[M]. is_formula(M,fml) \<longrightarrow>
             is_lambda
         (M, fml, is_formula_case (M, is_a, is_b, is_c(f), is_d(f)), z)"

  assumes a_closed: "[|x\<in>nat; y\<in>nat|] ==> M(a(x,y))"
      and a_rel:    "Relation2(M, nat, nat, is_a, a)"
      and b_closed: "[|x\<in>nat; y\<in>nat|] ==> M(b(x,y))"
      and b_rel:    "Relation2(M, nat, nat, is_b, b)"
      and c_closed: "[|x \<in> formula; y \<in> formula; M(gx); M(gy)|]
                     ==> M(c(x, y, gx, gy))"
      and c_rel:
         "M(f) ==>
          Relation2 (M, formula, formula, is_c(f),
             \<lambda>u v. c(u, v, f ` succ(depth(u)) ` u, f ` succ(depth(v)) ` v))"
      and d_closed: "[|x \<in> formula; M(gx)|] ==> M(d(x, gx))"
      and d_rel:
         "M(f) ==>
          Relation1(M, formula, is_d(f), \<lambda>u. d(u, f ` succ(depth(u)) ` u))"
      and fr_replace: "n \<in> nat ==> transrec_replacement(M,MH,n)"
      and fr_lam_replace:
           "M(g) ==>
            strong_replacement
              (M, \<lambda>x y. x \<in> formula &
                  y = \<langle>x, formula_rec_case(a,b,c,d,g,x)\<rangle>)"

lemma (in Formula_Rec) formula_rec_case_closed:
    "[|M(g); p \<in> formula|] ==> M(formula_rec_case(a, b, c, d, g, p))"
by (simp add: formula_rec_case_def a_closed b_closed c_closed d_closed)

lemma (in Formula_Rec) formula_rec_lam_closed:
    "M(g) ==> M(Lambda (formula, formula_rec_case(a,b,c,d,g)))"
by (simp add: lam_closed2 fr_lam_replace formula_rec_case_closed)

lemma (in Formula_Rec) MH_rel2:
     "relation2 (M, MH,
             \<lambda>x h. Lambda (formula, formula_rec_case(a,b,c,d,h)))"
apply (simp add: relation2_def MH_def, clarify)
apply (rule lambda_abs2)
apply (rule Relation1_formula_rec_case)
apply (simp_all add: a_rel b_rel c_rel d_rel formula_rec_case_closed)
done

lemma (in Formula_Rec) fr_transrec_closed:
    "n \<in> nat
     ==> M(transrec
          (n, \<lambda>x h. Lambda(formula, formula_rec_case(a, b, c, d, h))))"
by (simp add: transrec_closed [OF fr_replace MH_rel2]
              nat_into_M formula_rec_lam_closed)

text\<open>The main two results: \<^term>\<open>formula_rec\<close> is absolute for \<^term>\<open>M\<close>.\<close>
theorem (in Formula_Rec) formula_rec_closed:
    "p \<in> formula ==> M(formula_rec(a,b,c,d,p))"
by (simp add: formula_rec_eq fr_transrec_closed
              transM [OF _ formula_closed])

theorem (in Formula_Rec) formula_rec_abs:
  "[| p \<in> formula; M(z)|]
   ==> is_formula_rec(M,MH,p,z) \<longleftrightarrow> z = formula_rec(a,b,c,d,p)"
by (simp add: is_formula_rec_def formula_rec_eq transM [OF _ formula_closed]
              transrec_abs [OF fr_replace MH_rel2] depth_type
              fr_transrec_closed formula_rec_lam_closed eq_commute)


end
