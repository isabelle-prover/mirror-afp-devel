(*  ID:         $Id: QElin.thy,v 1.2 2008-01-11 15:22:26 lsf37 Exp $
    Author:     Tobias Nipkow, 2007
*)

theory QElin
imports LinArith
begin

subsection{* Fourier *}

definition qe_less :: "atom list \<Rightarrow> atom fm" where
"qe_less as = list_conj [Atom(combine p q). p\<leftarrow>lbounds as, q\<leftarrow>ubounds as]"

theorem I_qe_less:
assumes less: "\<forall>a \<in> set as. is_Less a" and dep: "\<forall>a \<in> set as. depends\<^isub>R a"
shows "R.I (qe_less as) xs = (\<exists>x. \<forall>a \<in> set as. I\<^isub>R a (x#xs))"  (is "?L = ?R")
proof
  let ?Ls = "set(lbounds as)" let ?Us = "set(ubounds as)"
  let ?lbs = "UN (r,cs):?Ls. {r + \<langle>cs,xs\<rangle>}"
  let ?ubs = "UN (r,cs):?Us. {r + \<langle>cs,xs\<rangle>}"
  have fins: "finite ?lbs \<and> finite ?ubs" by auto
  have 2: "\<forall>f\<in> set as. \<exists>r c cs. f = Less r (c#cs) \<and>
          (c>0 \<and> (r/c,(-1/c)*\<^sub>s cs) \<in> ?Ls \<or> c<0 \<and> (r/c,(-1/c)*\<^sub>s cs) \<in> ?Us)"
    using dep less
    by(fastsimp simp:set_lbounds set_ubounds is_Less_iff depends\<^isub>R_def
                split:list.splits)
  assume ?L
  have 1: "\<forall>x\<in>?lbs. \<forall>y\<in>?ubs. x < y"
  proof (rule ballI)+
    fix x y assume "x\<in>?lbs" "y\<in>?ubs"
    then obtain r cs
      where "(r,cs) \<in> ?Ls \<and> x = r + \<langle>cs,xs\<rangle>" by fastsimp
    moreover from `y\<in>?ubs` obtain s ds
      where "(s,ds) \<in> ?Us \<and> y = s + \<langle>ds,xs\<rangle>" by fastsimp
    ultimately show "x<y" using `?L`
      by(fastsimp simp:qe_less_def ring_simps iprod_left_diff_distrib)
  qed
  { assume nonempty: "?lbs \<noteq> {} \<and> ?ubs \<noteq> {}"
    hence "Max ?lbs < Min ?ubs" using fins 1
      by(blast intro: Max_less_iff[THEN iffD2] Min_gr_iff[THEN iffD2])
    then obtain m where "Max ?lbs < m \<and> m < Min ?ubs"
      using dense[where 'a = real] by blast
    hence "\<forall>a \<in> set as. I\<^isub>R a (m#xs)" using 2 nonempty
      by (auto simp:Ball_def Bex_def)(fastsimp simp:field_simps iprod_assoc)
    hence ?R .. }
  moreover
  { assume asm: "?lbs \<noteq> {} \<and> ?ubs = {}"
    have "\<forall>a \<in> set as. I\<^isub>R a ((Max ?lbs + 1) # xs)"
    proof
      fix a assume "a \<in> set as"
      then obtain r c cs
	where "a = Less r (c#cs)" "c>0" "(r/c,(-1/c)*\<^sub>s cs) \<in> ?Ls"
	using asm 2 by fastsimp
      moreover hence "(r - \<langle>cs,xs\<rangle>)/c \<le> Max ?lbs"
	using asm fins
	by(auto intro!: Max_ge_iff[THEN iffD2])
          (force simp add:field_simps iprod_assoc)
      ultimately show "I\<^isub>R a ((Max ?lbs + 1) # xs)" by (simp add: field_simps)
    qed
    hence ?R .. }
  moreover
  { assume asm: "?lbs = {} \<and> ?ubs \<noteq> {}"
    have "\<forall>a \<in> set as. I\<^isub>R a ((Min ?ubs - 1) # xs)"
    proof
      fix a assume "a \<in> set as"
      then obtain r c cs
	where "a = Less r (c#cs)" "c<0" "(r/c,(-1/c)*\<^sub>s cs) \<in> ?Us"
	using asm 2 by fastsimp
      moreover hence "Min ?ubs \<le> (r - \<langle>cs,xs\<rangle>)/c"
	using asm fins
	by(auto intro!: Min_le_iff[THEN iffD2])
          (force simp add:field_simps iprod_assoc)
      ultimately show "I\<^isub>R a ((Min ?ubs - 1) # xs)" by (simp add: field_simps)
    qed
    hence ?R .. }
  moreover
  { assume "?lbs = {} \<and> ?ubs = {}"
    hence ?R using 2 less by auto (rule, fast)
  }
  ultimately show ?R by blast
next
  let ?Ls = "set(lbounds as)" let ?Us = "set(ubounds as)"
  assume ?R
  then obtain x where 1: "\<forall>a\<in> set as. I\<^isub>R a (x#xs)" ..
  { fix r c cs s d ds
    assume "Less r (c#cs) \<in> set as" "0 < c" "Less s (d#ds) \<in> set as" "d < 0"
    hence "r < c*x + \<langle>cs,xs\<rangle>" "s < d*x + \<langle>ds,xs\<rangle>" "c > 0" "d < 0"
      using 1 by auto
    hence "(r - \<langle>cs,xs\<rangle>)/c < x" "x < (s - \<langle>ds,xs\<rangle>)/d" by(simp add:field_simps)+
    hence "(r - \<langle>cs,xs\<rangle>)/c < (s - \<langle>ds,xs\<rangle>)/d" by arith
  }
  thus ?L by (auto simp: qe_less_def iprod_left_diff_distrib iprod_assoc less field_simps set_lbounds set_ubounds)
qed

corollary I_qe_less_pretty:
  "\<forall>a \<in> set as. is_Less a \<and> depends\<^isub>R a \<Longrightarrow> R.is_dnf_qe qe_less as"
by(metis I_qe_less)


fun subst\<^isub>0 :: "atom \<Rightarrow> atom \<Rightarrow> atom" where
"subst\<^isub>0 (Eq r (c#cs)) a = (case a of
   Less s (d#ds) \<Rightarrow> Less (s - (r*d)/c) (ds - (d/c) *\<^sub>s cs)
 | Eq s (d#ds) \<Rightarrow> Eq (s - (r*d)/c) (ds - (d/c) *\<^sub>s cs))"

lemma subst\<^isub>0_pretty:
 "subst\<^isub>0 (Eq r (c#cs)) (Less s (d#ds)) = Less (s - (r*d)/c) (ds - (d/c) *\<^sub>s cs)"
 "subst\<^isub>0 (Eq r (c#cs)) (Eq s (d#ds)) = Eq (s - (r*d)/c) (ds - (d/c) *\<^sub>s cs)"
by auto

lemma I_subst\<^isub>0: "depends\<^isub>R a \<Longrightarrow> c \<noteq> 0 \<Longrightarrow>
       I\<^isub>R (subst\<^isub>0 (Eq r (c#cs)) a) xs = I\<^isub>R a ((r - \<langle>cs,xs\<rangle>)/c # xs)"
apply(cases a)
by (auto simp add: depends\<^isub>R_def iprod_assoc iprod_left_diff_distrib ring_simps diff_divide_distrib split:list.splits)

interpretation R\<^isub>e:
  ATOM_EQ[neg\<^isub>R "(\<lambda>a. True)" I\<^isub>R depends\<^isub>R decr\<^isub>R
          "(\<lambda>Eq _ (c#_) \<Rightarrow> c \<noteq> 0 | _ \<Rightarrow> False)"
          "(\<lambda>Eq r cs \<Rightarrow> r=0 \<and> (\<forall>c\<in> set cs. c=0) | _ \<Rightarrow> False)" subst\<^isub>0]
apply(unfold_locales)
   apply(simp del:subst\<^isub>0.simps add:I_subst\<^isub>0 split:atom.splits list.splits)
  apply(simp add: iprod0_if_coeffs0 split:atom.splits)
 apply(simp split:atom.splits list.splits)
 apply(rename_tac r ds c cs)
 apply(rule_tac x= "(r - \<langle>cs,xs\<rangle>)/c" in exI)
 apply (simp add: ring_simps diff_divide_distrib)
apply(simp add: self_list_diff set_replicate_conv_if
        split:atom.splits list.splits)
done

(* FIXME does not help
setup {* Sign.revert_abbrev "" @{const_name R\<^isub>e.lift_dnfeq_qe} *}
*)

definition "lin_qe = R\<^isub>e.lift_dnfeq_qe qe_less"

lemma qfree_qe_less: "qfree (qe_less as)"
by(auto simp:qe_less_def intro!:qfree_list_conj)

corollary I_lin_qe: "R.I (lin_qe \<phi>) xs = R.I \<phi> xs"
unfolding lin_qe_def
apply(rule R\<^isub>e.I_lift_dnfeq_qe)
 apply(rule qfree_qe_less)
apply(rule allI)
apply(rule I_qe_less)
 prefer 2 apply blast
apply(clarify)
apply(drule_tac x=a in bspec) apply simp
apply(simp add: depends\<^isub>R_def split:atom.splits list.splits)
done

theorem qfree_lin_qe: "qfree (lin_qe f)"
by(simp add:lin_qe_def R\<^isub>e.qfree_lift_dnfeq_qe qfree_qe_less)

subsubsection{* Tests *}

lemmas qesimps = lin_qe_def R\<^isub>e.lift_dnfeq_qe_def R\<^isub>e.lift_eq_qe_def R.qelim_def qe_less_def lbounds_def ubounds_def list_conj_def list_disj_def and_def or_def depends\<^isub>R_def

lemma "lin_qe(TrueF) = TrueF"
by(simp add:qesimps)

lemma
  "lin_qe(ExQ (And (Atom(Less 0 [1])) (Atom(Less 0 [-1])))) = Atom(Less 0 [])"
by(simp add:qesimps)

lemma
 "lin_qe(ExQ (And (Atom(Less 0 [1])) (Atom(Less -1 [-1])))) = Atom(Less -1 [])"
by(simp add:qesimps)

end
