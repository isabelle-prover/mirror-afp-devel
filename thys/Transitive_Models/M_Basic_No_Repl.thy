theory M_Basic_No_Repl
  imports "ZF-Constructible.Relative"
begin

txt\<open>This locale is exactly \<^locale>\<open>M_basic\<close> without its only replacement
instance.\<close>

locale M_basic_no_repl = M_trivial +
  assumes Inter_separation:
    "M(A) ==> separation(M, \<lambda>x. \<forall>y[M]. y\<in>A \<longrightarrow> x\<in>y)"
    and Diff_separation:
    "M(B) ==> separation(M, \<lambda>x. x \<notin> B)"
    and cartprod_separation:
    "[| M(A); M(B) |]
      ==> separation(M, \<lambda>z. \<exists>x[M]. x\<in>A & (\<exists>y[M]. y\<in>B & pair(M,x,y,z)))"
    and image_separation:
    "[| M(A); M(r) |]
      ==> separation(M, \<lambda>y. \<exists>p[M]. p\<in>r & (\<exists>x[M]. x\<in>A & pair(M,x,y,p)))"
    and converse_separation:
    "M(r) ==> separation(M,
         \<lambda>z. \<exists>p[M]. p\<in>r & (\<exists>x[M]. \<exists>y[M]. pair(M,x,y,p) & pair(M,y,x,z)))"
    and restrict_separation:
    "M(A) ==> separation(M, \<lambda>z. \<exists>x[M]. x\<in>A & (\<exists>y[M]. pair(M,x,y,z)))"
    and comp_separation:
    "[| M(r); M(s) |]
      ==> separation(M, \<lambda>xz. \<exists>x[M]. \<exists>y[M]. \<exists>z[M]. \<exists>xy[M]. \<exists>yz[M].
                  pair(M,x,z,xz) & pair(M,x,y,xy) & pair(M,y,z,yz) &
                  xy\<in>s & yz\<in>r)"
    and pred_separation:
    "[| M(r); M(x) |] ==> separation(M, \<lambda>y. \<exists>p[M]. p\<in>r & pair(M,y,x,p))"
    and Memrel_separation:
    "separation(M, \<lambda>z. \<exists>x[M]. \<exists>y[M]. pair(M,x,y,z) & x \<in> y)"
    and is_recfun_separation:
    \<comment> \<open>for well-founded recursion: used to prove \<open>is_recfun_equal\<close>\<close>
    "[| M(r); M(f); M(g); M(a); M(b) |]
     ==> separation(M,
            \<lambda>x. \<exists>xa[M]. \<exists>xb[M].
                pair(M,x,a,xa) & xa \<in> r & pair(M,x,b,xb) & xb \<in> r &
                (\<exists>fx[M]. \<exists>gx[M]. fun_apply(M,f,x,fx) & fun_apply(M,g,x,gx) &
                                   fx \<noteq> gx))"
    and power_ax:         "power_ax(M)"

lemma (in M_basic_no_repl) cartprod_iff:
  "[| M(A); M(B); M(C) |]
      ==> cartprod(M,A,B,C) \<longleftrightarrow>
          (\<exists>p1[M]. \<exists>p2[M]. powerset(M,A \<union> B,p1) & powerset(M,p1,p2) &
                   C = {z \<in> p2. \<exists>x\<in>A. \<exists>y\<in>B. z = <x,y>})"
  apply (simp add: Pair_def cartprod_def, safe)
    defer 1
    apply (simp add: powerset_def)
   apply blast
  txt\<open>Final, difficult case: the left-to-right direction of the theorem.\<close>
  apply (insert power_ax, simp add: power_ax_def)
  apply (frule_tac x="A \<union> B" and P="\<lambda>x. rex(M,Q(x))" for Q in rspec)
   apply (blast, clarify)
  apply (drule_tac x=z and P="\<lambda>x. rex(M,Q(x))" for Q in rspec)
   apply assumption
  apply (blast intro: cartprod_iff_lemma)
  done

lemma (in M_basic_no_repl) cartprod_closed_lemma:
  "[| M(A); M(B) |] ==> \<exists>C[M]. cartprod(M,A,B,C)"
  apply (simp del: cartprod_abs add: cartprod_iff)
  apply (insert power_ax, simp add: power_ax_def)
  apply (frule_tac x="A \<union> B" and P="\<lambda>x. rex(M,Q(x))" for Q in rspec)
   apply (blast, clarify)
  apply (drule_tac x=z and P="\<lambda>x. rex(M,Q(x))" for Q in rspec, auto)
  apply (intro rexI conjI, simp+)
  apply (insert cartprod_separation [of A B], simp)
  done

text\<open>All the lemmas above are necessary because Powerset is not absolute.
      I should have used Replacement instead!\<close>
lemma (in M_basic_no_repl) cartprod_closed [intro,simp]:
  "[| M(A); M(B) |] ==> M(A*B)"
  by (frule cartprod_closed_lemma, assumption, force)

lemma (in M_basic_no_repl) sum_closed [intro,simp]:
  "[| M(A); M(B) |] ==> M(A+B)"
  by (simp add: sum_def)

lemma (in M_basic_no_repl) sum_abs [simp]:
  "[| M(A); M(B); M(Z) |] ==> is_sum(M,A,B,Z) \<longleftrightarrow> (Z = A+B)"
  by (simp add: is_sum_def sum_def singleton_0 nat_into_M)

lemma (in M_basic_no_repl) M_converse_iff:
  "M(r) ==>
      converse(r) =
      {z \<in> \<Union>(\<Union>(r)) * \<Union>(\<Union>(r)).
       \<exists>p\<in>r. \<exists>x[M]. \<exists>y[M]. p = \<langle>x,y\<rangle> & z = \<langle>y,x\<rangle>}"
  apply (rule equalityI)
   prefer 2 apply (blast dest: transM, clarify, simp)
  apply (simp add: Pair_def)
  apply (blast dest: transM)
  done

lemma (in M_basic_no_repl) converse_closed [intro,simp]:
  "M(r) ==> M(converse(r))"
  apply (simp add: M_converse_iff)
  apply (insert converse_separation [of r], simp)
  done

lemma (in M_basic_no_repl) converse_abs [simp]:
  "[| M(r); M(z) |] ==> is_converse(M,r,z) \<longleftrightarrow> z = converse(r)"
  apply (simp add: is_converse_def)
  apply (rule iffI)
   prefer 2 apply blast
  apply (rule M_equalityI)
    apply simp
    apply (blast dest: transM)+
  done


subsubsection \<open>image, preimage, domain, range\<close>

lemma (in M_basic_no_repl) image_closed [intro,simp]:
  "[| M(A); M(r) |] ==> M(r``A)"
  apply (simp add: image_iff_Collect)
  apply (insert image_separation [of A r], simp)
  done

lemma (in M_basic_no_repl) vimage_abs [simp]:
  "[| M(r); M(A); M(z) |] ==> pre_image(M,r,A,z) \<longleftrightarrow> z = r-``A"
  apply (simp add: pre_image_def)
  apply (rule iffI)
   apply (blast intro!: equalityI dest: transM, blast)
  done

lemma (in M_basic_no_repl) vimage_closed [intro,simp]:
  "[| M(A); M(r) |] ==> M(r-``A)"
  by (simp add: vimage_def)


subsubsection\<open>Domain, range and field\<close>

lemma (in M_basic_no_repl) domain_closed [intro,simp]:
  "M(r) ==> M(domain(r))"
  apply (simp add: domain_eq_vimage)
  done

lemma (in M_basic_no_repl) range_closed [intro,simp]:
  "M(r) ==> M(range(r))"
  apply (simp add: range_eq_image)
  done

lemma (in M_basic_no_repl) field_abs [simp]:
  "[| M(r); M(z) |] ==> is_field(M,r,z) \<longleftrightarrow> z = field(r)"
  by (simp add: is_field_def field_def)

lemma (in M_basic_no_repl) field_closed [intro,simp]:
  "M(r) ==> M(field(r))"
  by (simp add: field_def)


subsubsection\<open>Relations, functions and application\<close>

lemma (in M_basic_no_repl) apply_closed [intro,simp]:
  "[|M(f); M(a)|] ==> M(f`a)"
  by (simp add: apply_def)

lemma (in M_basic_no_repl) apply_abs [simp]:
  "[| M(f); M(x); M(y) |] ==> fun_apply(M,f,x,y) \<longleftrightarrow> f`x = y"
  apply (simp add: fun_apply_def apply_def, blast)
  done

lemma (in M_basic_no_repl) injection_abs [simp]:
  "[| M(A); M(f) |] ==> injection(M,A,B,f) \<longleftrightarrow> f \<in> inj(A,B)"
  apply (simp add: injection_def apply_iff inj_def)
  apply (blast dest: transM [of _ A])
  done

lemma (in M_basic_no_repl) surjection_abs [simp]:
  "[| M(A); M(B); M(f) |] ==> surjection(M,A,B,f) \<longleftrightarrow> f \<in> surj(A,B)"
  by (simp add: surjection_def surj_def)

lemma (in M_basic_no_repl) bijection_abs [simp]:
  "[| M(A); M(B); M(f) |] ==> bijection(M,A,B,f) \<longleftrightarrow> f \<in> bij(A,B)"
  by (simp add: bijection_def bij_def)


subsubsection\<open>Composition of relations\<close>

lemma (in M_basic_no_repl) M_comp_iff:
  "[| M(r); M(s) |]
      ==> r O s =
          {xz \<in> domain(s) * range(r).
            \<exists>x[M]. \<exists>y[M]. \<exists>z[M]. xz = \<langle>x,z\<rangle> & \<langle>x,y\<rangle> \<in> s & \<langle>y,z\<rangle> \<in> r}"
  apply (simp add: comp_def)
  apply (rule equalityI)
   apply clarify
   apply simp
   apply  (blast dest:  transM)+
  done

lemma (in M_basic_no_repl) comp_closed [intro,simp]:
  "[| M(r); M(s) |] ==> M(r O s)"
  apply (simp add: M_comp_iff)
  apply (insert comp_separation [of r s], simp)
  done

lemma (in M_basic_no_repl) composition_abs [simp]:
  "[| M(r); M(s); M(t) |] ==> composition(M,r,s,t) \<longleftrightarrow> t = r O s"
  apply safe
  txt\<open>Proving \<^term>\<open>composition(M, r, s, r O s)\<close>\<close>
   prefer 2
   apply (simp add: composition_def comp_def)
   apply (blast dest: transM)
  txt\<open>Opposite implication\<close>
  apply (rule M_equalityI)
    apply (simp add: composition_def comp_def)
    apply (blast del: allE dest: transM)+
  done

text\<open>no longer needed\<close>
lemma (in M_basic_no_repl) restriction_is_function:
  "[| restriction(M,f,A,z); function(f); M(f); M(A); M(z) |]
      ==> function(z)"
  apply (simp add: restriction_def ball_iff_equiv)
  apply (unfold function_def, blast)
  done

lemma (in M_basic_no_repl) restrict_closed [intro,simp]:
  "[| M(A); M(r) |] ==> M(restrict(r,A))"
  apply (simp add: M_restrict_iff)
  apply (insert restrict_separation [of A], simp)
  done

lemma (in M_basic_no_repl) Inter_closed [intro,simp]:
  "M(A) ==> M(\<Inter>(A))"
  by (insert Inter_separation, simp add: Inter_def)

lemma (in M_basic_no_repl) Int_closed [intro,simp]:
  "[| M(A); M(B) |] ==> M(A \<inter> B)"
  apply (subgoal_tac "M({A,B})")
   apply (frule Inter_closed, force+)
  done

lemma (in M_basic_no_repl) Diff_closed [intro,simp]:
  "[|M(A); M(B)|] ==> M(A-B)"
  by (insert Diff_separation, simp add: Diff_def)

subsubsection\<open>Some Facts About Separation Axioms\<close>

lemma (in M_basic_no_repl) separation_conj:
  "[|separation(M,P); separation(M,Q)|] ==> separation(M, \<lambda>z. P(z) & Q(z))"
  by (simp del: separation_closed
      add: separation_iff Collect_Int_Collect_eq [symmetric])

lemma (in M_basic_no_repl) separation_disj:
  "[|separation(M,P); separation(M,Q)|] ==> separation(M, \<lambda>z. P(z) | Q(z))"
  by (simp del: separation_closed
      add: separation_iff Collect_Un_Collect_eq [symmetric])

lemma (in M_basic_no_repl) separation_neg:
  "separation(M,P) ==> separation(M, \<lambda>z. ~P(z))"
  by (simp del: separation_closed
      add: separation_iff Diff_Collect_eq [symmetric])

lemma (in M_basic_no_repl) separation_imp:
  "[|separation(M,P); separation(M,Q)|]
      ==> separation(M, \<lambda>z. P(z) \<longrightarrow> Q(z))"
  by (simp add: separation_neg separation_disj not_disj_iff_imp [symmetric])

text\<open>This result is a hint of how little can be done without the Reflection
  Theorem.  The quantifier has to be bounded by a set.  We also need another
  instance of Separation!\<close>
lemma (in M_basic_no_repl) separation_rall:
  "[|M(Y); \<forall>y[M]. separation(M, \<lambda>x. P(x,y));
        \<forall>z[M]. strong_replacement(M, \<lambda>x y. y = {u \<in> z . P(u,x)})|]
      ==> separation(M, \<lambda>x. \<forall>y[M]. y\<in>Y \<longrightarrow> P(x,y))"
  apply (simp del: separation_closed rall_abs
      add: separation_iff Collect_rall_eq)
  apply (blast intro!:  RepFun_closed dest: transM)
  done


subsubsection\<open>Functions and function space\<close>

lemma (in M_basic_no_repl) succ_fun_eq2:
  "[|M(B); M(n->B)|] ==>
      succ(n) -> B =
      \<Union>{z. p \<in> (n->B)*B, \<exists>f[M]. \<exists>b[M]. p = <f,b> & z = {cons(<n,b>, f)}}"
  apply (simp add: succ_fun_eq)
  apply (blast dest: transM)
  done

(* lemma (in M_basic_no_repl) funspace_succ:
     "[|M(n); M(B); M(n->B) |] ==> M(succ(n) -> B)"
apply (insert funspace_succ_replacement [of n], simp)
apply (force simp add: succ_fun_eq2 univalent_def)
done

text\<open>\<^term>\<open>M\<close> contains all finite function spaces.  Needed to prove the
absoluteness of transitive closure.  See the definition of
\<open>rtrancl_alt\<close> in in \<open>WF_absolute.thy\<close>.\<close>
lemma (in M_basic_no_repl) finite_funspace_closed [intro,simp]:
     "[|n\<in>nat; M(B)|] ==> M(n->B)"
apply (induct_tac n, simp)
apply (simp add: funspace_succ nat_into_M)
done
 *)

lemma (in M_basic_no_repl) list_case'_closed [intro,simp]:
  "[|M(k); M(a); \<forall>x[M]. \<forall>y[M]. M(b(x,y))|] ==> M(list_case'(a,b,k))"
  apply (case_tac "quasilist(k)")
   apply (simp add: quasilist_def, force)
  apply (simp add: non_list_case)
  done

lemma (in M_basic_no_repl) tl'_closed: "M(x) ==> M(tl'(x))"
  apply (simp add: tl'_def)
  apply (force simp add: quasilist_def)
  done

sublocale M_basic \<subseteq> mbnr:M_basic_no_repl
  using Inter_separation Diff_separation cartprod_separation image_separation
    converse_separation restrict_separation comp_separation pred_separation
    Memrel_separation is_recfun_separation power_ax by unfold_locales

end
