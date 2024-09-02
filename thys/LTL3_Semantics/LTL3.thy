theory LTL3
  imports Main Traces AnswerIndexedFamilies LinearTemporalLogic
begin

chapter \<open>LTL3: Semantics, Equivalence and Formula Progression\<close>

type_synonym 'a AiF\<^sub>3 = \<open>answer \<Rightarrow> 'a state dset\<close>

primrec and_AiF\<^sub>3 :: \<open>'a AiF\<^sub>3 \<Rightarrow> 'a AiF\<^sub>3 \<Rightarrow> 'a AiF\<^sub>3\<close> (infixl \<open>\<and>\<^sub>3\<sqdot>\<close> 60) where
  \<open>(a \<and>\<^sub>3\<sqdot> b) T = a T \<sqinter> b T\<close>
| \<open>(a \<and>\<^sub>3\<sqdot> b) F = a F \<squnion> b F\<close>

primrec or_AiF\<^sub>3 :: \<open>'a AiF\<^sub>3 \<Rightarrow> 'a AiF\<^sub>3 \<Rightarrow> 'a AiF\<^sub>3\<close> (infixl \<open>\<or>\<^sub>3\<sqdot>\<close> 59) where
  \<open>(a \<or>\<^sub>3\<sqdot> b) T = a T \<squnion> b T\<close>
| \<open>(a \<or>\<^sub>3\<sqdot> b) F = a F \<sqinter> b F\<close>

fun not_AiF\<^sub>3 :: \<open>'a AiF\<^sub>3 \<Rightarrow> 'a AiF\<^sub>3\<close> (\<open>\<not>\<^sub>3\<sqdot> _\<close>) where
  \<open>(\<not>\<^sub>3\<sqdot> a) T = a F\<close>
| \<open>(\<not>\<^sub>3\<sqdot> a) F = a T\<close>

fun univ_AiF\<^sub>3 :: \<open>'a AiF\<^sub>3\<close> (\<open>T\<^sub>3\<bullet>\<close>) where
  \<open>T\<^sub>3\<bullet> T = \<Sigma>\<infinity>\<close>
| \<open>T\<^sub>3\<bullet> F = \<emptyset>\<close>

fun lsatisfying_AiF\<^sub>3 :: \<open>'a \<Rightarrow> 'a AiF\<^sub>3\<close> (\<open>lsat\<^sub>3\<bullet>\<close>) where
  \<open>lsat\<^sub>3\<bullet> x T = compr (\<lambda>t. t \<noteq> \<epsilon> \<and> x \<in> L (thead t))\<close>
| \<open>lsat\<^sub>3\<bullet> x F = compr (\<lambda>t. t \<noteq> \<epsilon> \<and> x \<notin> L (thead t))\<close>

fun x\<^sub>3_operator :: \<open>'a AiF\<^sub>3 \<Rightarrow> 'a AiF\<^sub>3\<close> (\<open>X\<^sub>3\<sqdot>\<close>) where
  \<open>X\<^sub>3\<sqdot> t T = prepend (t T)\<close>
| \<open>X\<^sub>3\<sqdot> t F = prepend (t F)\<close>

fun iterate :: \<open>('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a)\<close> where
\<open>iterate f 0 x = x\<close>|
\<open>iterate f (Suc n) x = f (iterate f n x)\<close>

primrec u\<^sub>3_operator :: \<open>'a AiF\<^sub>3 \<Rightarrow> 'a AiF\<^sub>3 \<Rightarrow> 'a AiF\<^sub>3\<close> (infix \<open>U\<^sub>3\<sqdot>\<close> 61) where
  \<open>(a U\<^sub>3\<sqdot> b) T = \<Squnion> ( range (\<lambda>i. iterate (\<lambda>x. prepend x \<sqinter> a T) i (b T) ))\<close>
| \<open>(a U\<^sub>3\<sqdot> b) F = \<Sqinter> ( range (\<lambda>i. iterate (\<lambda>x. prepend x \<squnion> a F) i (b F) ))\<close>

fun triv_true :: \<open>'a \<Rightarrow> bool\<close> where
\<open>triv_true x = (\<forall>s. x\<in> L s)\<close>

fun triv_false :: \<open>'a \<Rightarrow> bool\<close> where
\<open>triv_false x = (\<forall>s. x\<notin> L s)\<close>

fun nontrivial :: \<open>'a \<Rightarrow> bool\<close> where
\<open>nontrivial x = ((\<exists>s. x\<in> L s) \<and> (\<exists>t. x\<notin> L t))\<close>

fun zero_length :: \<open>'a trace \<Rightarrow> bool\<close> where
  \<open>zero_length (Finite t) = (length t = 0)\<close>
| \<open>zero_length (Infinite t) = False\<close>

fun ltl_semantics\<^sub>3 :: \<open>'a ltl \<Rightarrow> 'a AiF\<^sub>3\<close> (\<open>\<lbrakk>_\<rbrakk>\<^sub>3\<close>) where
  \<open>\<lbrakk> true\<^sub>l    \<rbrakk>\<^sub>3 = T\<^sub>3\<bullet>\<close>
| \<open>\<lbrakk> not\<^sub>l \<phi>   \<rbrakk>\<^sub>3 = \<not>\<^sub>3\<sqdot> \<lbrakk>\<phi>\<rbrakk>\<^sub>3\<close>
| \<open>\<lbrakk> prop\<^sub>l(a) \<rbrakk>\<^sub>3 = lsat\<^sub>3\<bullet> a\<close>
| \<open>\<lbrakk> \<phi> or\<^sub>l \<psi>  \<rbrakk>\<^sub>3 = \<lbrakk>\<phi>\<rbrakk>\<^sub>3 \<or>\<^sub>3\<sqdot> \<lbrakk>\<psi>\<rbrakk>\<^sub>3\<close>
| \<open>\<lbrakk> \<phi> and\<^sub>l \<psi> \<rbrakk>\<^sub>3 = \<lbrakk>\<phi>\<rbrakk>\<^sub>3 \<and>\<^sub>3\<sqdot> \<lbrakk>\<psi>\<rbrakk>\<^sub>3\<close>
| \<open>\<lbrakk> X\<^sub>l \<phi>     \<rbrakk>\<^sub>3 = X\<^sub>3\<sqdot> \<lbrakk>\<phi>\<rbrakk>\<^sub>3\<close>
| \<open>\<lbrakk> \<phi> U\<^sub>l \<psi>   \<rbrakk>\<^sub>3 = \<lbrakk>\<phi>\<rbrakk>\<^sub>3 U\<^sub>3\<sqdot> \<lbrakk>\<psi>\<rbrakk>\<^sub>3\<close>

section \<open>LTL/LTL3 equivalence\<close>

declare dset.Inf_insert[simp del]
declare dset.Sup_insert[simp del]

lemma itdrop_all_split:
  assumes \<open>x \<in> A\<close> and \<open>\<forall>i<k. itdrop (Suc i) x \<in> A\<close>
  shows \<open>i < Suc k \<Longrightarrow> itdrop i x \<in> A\<close>
using assms proof (cases \<open>i\<close>)
qed (auto simp: itdrop_def)

lemma itdrop_exists_split[simp]:
  shows \<open>(\<exists>i<Suc k. itdrop i x \<in> A) \<longleftrightarrow> (\<exists>i < k. itdrop (Suc i) x \<in> A) \<or> x \<in> A\<close>
proof (rule iffI)
{ fix i
  assume \<open>i < Suc k\<close> \<open>itdrop i x \<in> A\<close> \<open>x \<notin> A\<close>
  then have \<open>\<exists>i<k. itdrop (Suc i) x \<in> A\<close>
  proof (cases \<open>i\<close>)
  qed auto
} then show \<open> \<exists>i<Suc k. itdrop i x \<in> A \<Longrightarrow> (\<exists>i<k. itdrop (Suc i) x \<in> A) \<or> x \<in> A\<close> by auto
next
  assume \<open>(\<exists>i<k. itdrop (Suc i) x \<in> A) \<or> x \<in> A\<close>
  then show \<open>\<exists>i<Suc k. itdrop i x \<in> A\<close>
    by auto
qed

lemma until_iterate : 
  \<open>{x. \<exists>k. (\<forall>i<k. itdrop i x \<in> A) \<and> itdrop k x \<in> B} = \<Union> (range (\<lambda>k. iterate (\<lambda>x. iprepend x \<inter> A) k B))\<close>
proof (rule set_eqI; rule iffI)
  fix x 
{ fix k
  assume  \<open>\<forall>i<k. itdrop i x \<in> A \<close> and \<open>itdrop k x \<in> B\<close>
  then have \<open>x \<in> iterate (\<lambda>x. iprepend x \<inter> A) k B\<close>
  proof (induct \<open>k\<close> arbitrary: \<open>x\<close>)
    case 0
    then show \<open>?case\<close> by simp
  next
    case (Suc k)
    from this(2,3) show \<open>?case\<close> 
      by (auto intro!: Suc.hyps[where x = \<open>itdrop 1 x\<close>, simplified])
  qed }
  then show \<open>x \<in> {x. \<exists>k. (\<forall>i<k. itdrop i x \<in> A) \<and> itdrop k x \<in> B}
           \<Longrightarrow> x \<in> (\<Union>k. iterate (\<lambda>x. iprepend x \<inter> A) k B)\<close>
    by blast
next
  fix x 
{ fix k
  assume \<open>x \<in> iterate (\<lambda>x. iprepend x \<inter> A) k B\<close>
  then have \<open>(\<forall>i<k. itdrop i x \<in> A) \<and> itdrop k x \<in> B \<close>
  proof (induct \<open>k\<close> arbitrary: \<open>x\<close>)
    case 0
    then show \<open>?case\<close> by auto
  next
    case (Suc k)
    from this(2) show \<open>?case\<close>
      by (auto dest: Suc.hyps[where x = \<open>itdrop 1 x\<close>, simplified] 
               intro: itdrop_all_split)
  qed }
  then show \<open>x \<in> (\<Union>k. iterate (\<lambda>x. iprepend x \<inter> A) k B) \<Longrightarrow> x \<in> {x. \<exists>k. (\<forall>i<k. itdrop i x \<in> A) \<and> itdrop k x \<in> B}\<close>
    by blast
qed

lemma release_iterate:
  \<open> {u. \<forall>k. (\<exists>i<k. itdrop i u \<in> A) \<or> itdrop k u \<in> B} = \<Inter> (range (\<lambda>i. iterate (\<lambda>x. iprepend x \<union> A) i B))\<close>
proof (rule set_eqI; rule iffI)
  fix x 
{ fix i assume \<open> \<forall>k. (\<exists>i<k. itdrop i x \<in> A) \<or> itdrop k x \<in> B\<close>
  then have \<open>x \<in> iterate (\<lambda>x. iprepend x \<union> A) i B\<close>
  proof (induct \<open>i\<close> arbitrary: \<open>x\<close>)
    case 0
    then show \<open>?case\<close> by auto
  next
    case (Suc i)
    show \<open>?case\<close>
      apply (clarsimp)
      apply (rule Suc.hyps[where x = \<open>itdrop 1 x\<close>, simplified])
      using Suc(2)[THEN spec, where x = \<open>Suc _\<close>,simplified]
      by auto
  qed }
  then show \<open>x \<in> {u. \<forall>k. (\<exists>i<k. itdrop i u \<in> A) \<or> itdrop k u \<in> B} \<Longrightarrow> x \<in> (\<Inter>i. iterate (\<lambda>x. iprepend x \<union> A) i B)\<close>
    by auto
next
  fix x
{ fix k
  assume \<open> \<forall>i. x \<in> iterate (\<lambda>x. iprepend x \<union> A) i B\<close>
  then have P: \<open>\<forall>i. x \<in> iterate (\<lambda>x. iprepend x \<union> A) i B\<close> 
    by blast
  assume \<open>itdrop k x \<notin> B\<close> with P have \<open>\<exists>i<k. itdrop i x \<in> A\<close>
  proof (induct \<open>k\<close> arbitrary: \<open>x\<close>)
    case 0
    then show \<open>?case\<close> by (simp, metis iterate.simps(1))
  next
    case (Suc k)
    from this(3) show \<open>?case\<close>
      apply clarsimp
      apply (rule Suc.hyps[where x = \<open>itdrop 1 x\<close>, simplified])
      using Suc(2)[THEN spec, where x = \<open>Suc _\<close>]
      by auto
  qed }
  then show \<open>x \<in> (\<Inter>i. iterate (\<lambda>x. iprepend x \<union> A) i B) \<Longrightarrow> x \<in> {u. \<forall>k. (\<exists>i<k. itdrop i u \<in> A) \<or> itdrop k u \<in> B}\<close>
    by auto
qed

lemma property_until_iterate: 
  \<open>property (iterate (\<lambda>x. prepend x \<sqinter> A) k B) = iterate (\<lambda>x. iprepend x \<inter> property A) k (property B)\<close>
  by (induct \<open>k\<close>, auto simp: property_Inter property_prepend)

lemma property_release_iterate: 
  \<open>property (iterate (\<lambda>x. prepend x \<squnion> A) k B) = iterate (\<lambda>x. iprepend x \<union> property A) k (property B)\<close>
  by (induct \<open>k\<close>, auto simp: property_Union property_prepend)

lemma ltl3_equiv_ltl: 
  shows \<open>property (\<lbrakk> \<phi> \<rbrakk>\<^sub>3 T) = \<lbrakk> \<phi> \<rbrakk>\<^sub>l T\<close>
  and   \<open>property (\<lbrakk> \<phi> \<rbrakk>\<^sub>3 F) = \<lbrakk> \<phi> \<rbrakk>\<^sub>l F\<close>
proof (induct \<open>\<phi>\<close>)
  case True_ltl
  {
    case 1
    then show \<open>?case\<close> by (simp, transfer, simp)
  next
    case 2
    then show \<open>?case\<close> by (simp, transfer, simp)
  }
next
  case (Not_ltl \<phi>)
  {
    case 1
    then show \<open>?case\<close> using Not_ltl by simp
  next
    case 2
    then show \<open>?case\<close> using Not_ltl by simp
  }
next
  case (Prop_ltl x)
  {
    case 1
    then show \<open>?case\<close>
      apply simp
      apply transfer
      apply (simp add: infinites_dprefixes)
      apply (clarsimp simp add: infinites_def  split: trace.split_asm trace.split)
      apply (rule set_eqI, rule iffI)
       apply (clarsimp  split: trace.split_asm trace.split)
       apply (metis zero_length.cases)
       apply (clarsimp split: trace.split_asm trace.split)
      by (metis Traces.append.simps(3) append_is_empty(2) trace.distinct(1) trace.inject(2))
  next
    case 2
    then show \<open>?case\<close>
      apply simp
      apply transfer
      apply (simp add: infinites_dprefixes)
      apply (clarsimp simp add: infinites_def  split: trace.split_asm trace.split)
      apply (rule set_eqI, rule iffI)
       apply (clarsimp  split: trace.split_asm trace.split)
       apply (metis zero_length.cases)
       apply (clarsimp split: trace.split_asm trace.split)
      by (metis Traces.append.simps(3) append_is_empty(2) trace.distinct(1) trace.inject(2))
  }
next
  case (Or_ltl \<phi>1 \<phi>2)
  {
    case 1
    then show \<open>?case\<close> by (simp add: property_Union Or_ltl)
  next
    case 2
    then show \<open>?case\<close> by (simp add: property_Inter Or_ltl)
  }
next
  case (And_ltl \<phi>1 \<phi>2)
  {
    case 1
    then show \<open>?case\<close> by (simp add: property_Inter And_ltl)
  next
    case 2
    then show \<open>?case\<close> by (simp add: property_Union And_ltl)
  }
next
  case (Next_ltl \<phi>)
  {
    case 1
    then show \<open>?case\<close> by (simp add: property_prepend Next_ltl iprepend_def)
    next
    case 2
    then show \<open>?case\<close> by (simp add: property_prepend Next_ltl iprepend_def)
  }
next
  case (Until_ltl \<phi>1 \<phi>2)
  {
    case 1
    then show \<open>?case\<close>
      apply (simp add: Until_ltl[THEN sym] property_Union image_Collect property_until_iterate)
      using until_iterate[simplified] by blast 
  next
    case 2
    then show \<open>?case\<close> 
      apply (simp add: Until_ltl[THEN sym] property_Inter image_Collect property_release_iterate)
      using release_iterate[simplified] by metis
  }
qed

section \<open>Equivalence to LTL3 of Bauer et al.\<close>

lemma extension_lemma: \<open>in_dset t A = (\<forall>\<omega>. t \<frown> Infinite \<omega> \<in> Infinite ` property A)\<close>
proof transfer
  fix t and A :: \<open>'a trace set\<close>
  assume D: \<open>definitive A\<close> 
  show \<open>t \<in> A = (\<forall>\<omega>. t \<frown> Infinite \<omega> \<in> Infinite ` infinites A) \<close>
  proof (rule iffI)
    assume \<open>t \<in> A\<close>
    with D have D': \<open>\<up> t \<subseteq> A \<close> by (rule definitive_contains_extensions)
    { fix \<omega> have \<open>t \<frown> Infinite \<omega> \<in> A\<close>
        by (rule subsetD[OF D'], force simp add: extensions_def)
    } then have \<open> \<forall>\<omega>. t \<frown> Infinite \<omega> \<in>  A\<close> by auto
    thus  \<open> \<forall>\<omega>. t \<frown> Infinite \<omega> \<in> Infinite ` infinites A\<close>
      by (simp add: infinites_append_right infinites_alt)
  next
    assume \<open> \<forall>\<omega>. t \<frown> Infinite \<omega> \<in> Infinite ` infinites A\<close> then
    have inA: \<open> \<forall>\<omega>. t \<frown> Infinite \<omega> \<in> A\<close>
      by (simp add: infinites_alt infinites_append_right)
    have \<open>\<up> t \<subseteq> \<down>\<^sub>s A\<close> 
    proof -
      { fix u 
        obtain \<omega> :: \<open>'a infinite_trace\<close> where \<open>Infinite \<omega> = u \<frown> Infinite undefined\<close>
          by (cases \<open>u\<close>; simp)
        then have \<open>\<exists>v. (t \<frown> u) \<frown> v \<in> A\<close> 
          using inA[THEN spec, where x = \<open>\<omega>\<close>] by (metis trace.assoc)
      } thus \<open>?thesis\<close> unfolding extensions_def prefix_closure_def prefixes_def by auto
    qed
    with D show \<open>t \<in> A\<close> by (rule definitive_elemI)
  qed
qed

lemma extension: 
  shows \<open>in_dset t (ltl_semantics\<^sub>3 \<phi> T) = (\<forall>\<omega>. (t \<frown> Infinite \<omega>) \<in> Infinite ` (ltl_semantics \<phi> T))\<close>
  and   \<open>in_dset t (ltl_semantics\<^sub>3 \<phi> F) = (\<forall>\<omega>. (t \<frown> Infinite \<omega>) \<in> Infinite ` (ltl_semantics \<phi> F))\<close>
  by (simp_all add: ltl3_equiv_ltl[THEN sym] extension_lemma)

section \<open>Formula Progression\<close>

fun progress :: \<open>'a ltl \<Rightarrow> 'a state \<Rightarrow> 'a ltl\<close> where
  \<open>progress true\<^sub>l \<sigma> = true\<^sub>l\<close>
| \<open>progress (not\<^sub>l \<phi>) \<sigma> = not\<^sub>l (progress \<phi>) \<sigma>\<close>
| \<open>progress (prop\<^sub>l(a)) \<sigma> = (if a \<in> L \<sigma> then true\<^sub>l else not\<^sub>l true\<^sub>l)\<close>
| \<open>progress (\<phi> or\<^sub>l \<psi>) \<sigma> = (progress \<phi> \<sigma>) or\<^sub>l (progress \<psi> \<sigma>)\<close>
| \<open>progress (\<phi> and\<^sub>l \<psi>) \<sigma> = (progress \<phi> \<sigma>) and\<^sub>l (progress \<psi> \<sigma>)\<close>
| \<open>progress (X\<^sub>l \<phi>) \<sigma> = \<phi>\<close>
| \<open>progress (\<phi> U\<^sub>l \<psi>) \<sigma> = (progress \<psi> \<sigma>) or\<^sub>l ((progress \<phi> \<sigma>) and\<^sub>l (\<phi> U\<^sub>l \<psi>))\<close>

lemma unroll_Union: \<open>\<Squnion> (range P) = P 0 \<squnion> (\<Squnion> (range (P \<circ> Suc)))\<close>
  apply (rule definitives_inverse_eqI)
  apply (simp add: property_Union)
  apply (rule dset.order_antisym)
   apply (clarsimp intro!: definitives_mono; metis not0_implies_Suc)
  by (force intro: definitives_mono)

lemma unroll_Inter: \<open>\<Sqinter> (range P) = P 0 \<sqinter> (\<Sqinter> (range (P \<circ> Suc)))\<close>
  apply (rule definitives_inverse_eqI)
  apply (simp add: property_Inter)
  apply (rule dset.order_antisym)
   apply (force intro: definitives_mono)
  by (clarsimp intro!: definitives_mono; metis not0_implies_Suc)

lemma iterates_nonempty: \<open>range (\<lambda>i. iterate f i X) \<noteq> {}\<close>
  by blast

lemma until_cont: \<open>A \<noteq> {} \<Longrightarrow> prepend (\<Squnion> A) \<sqinter> X = \<Squnion> ((\<lambda>x. prepend x \<sqinter> X) ` A)\<close>
  by (simp add: prepend_Union[THEN sym] dset.SUP_inf)

lemma release_cont: \<open>A \<noteq> {} \<Longrightarrow> prepend (\<Sqinter> A) \<squnion> X = \<Sqinter> ((\<lambda>x. prepend x \<squnion> X) ` A)\<close>
  by (simp add: prepend_Inter[THEN sym] dset.INF_sup)

lemma iterate_unroll_Inter: 
  assumes \<open>\<And>A. A \<noteq> {} \<Longrightarrow> f (\<Sqinter> A) = \<Sqinter> (f ` A)\<close> 
  shows \<open>\<Sqinter> (range (\<lambda>i. iterate f i X)) = X \<sqinter> f (\<Sqinter> (range (\<lambda>i. iterate f i X )))\<close>
  apply (subst unroll_Inter)
  by (force simp: assms[OF iterates_nonempty] property_Inter intro: definitives_inverse_eqI)

lemma iterate_unroll_Union: 
  assumes \<open>\<And>A. A \<noteq> {} \<Longrightarrow> f (\<Squnion> A) = \<Squnion> (f ` A)\<close> 
  shows \<open>\<Squnion> (range (\<lambda>i. iterate f i X)) = X \<squnion> f (\<Squnion> (range (\<lambda>i. iterate f i X )))\<close>
  apply (subst unroll_Union)
  by (force simp: assms[OF iterates_nonempty] property_Union intro: definitives_inverse_eqI)


lemma inf_inf: \<open>x \<sqinter> (y \<sqinter> z) = (x \<sqinter> y) \<sqinter> (x \<sqinter> z)\<close>
  by (simp add: dset.inf_assoc dset.inf_left_commute)



theorem progression_tf :
  \<open>prepend (\<lbrakk>progress \<phi> \<sigma> \<rbrakk>\<^sub>3 T) \<sqinter> compr (\<lambda>t. t \<noteq> \<epsilon> \<and> thead t = \<sigma>) \<sqsubseteq> \<lbrakk> \<phi> \<rbrakk>\<^sub>3 T \<close>
  \<open>prepend (\<lbrakk>progress \<phi> \<sigma> \<rbrakk>\<^sub>3 F) \<sqinter> compr (\<lambda>t. t \<noteq> \<epsilon> \<and> thead t = \<sigma>) \<sqsubseteq> \<lbrakk> \<phi> \<rbrakk>\<^sub>3 F \<close>
proof (induct \<open>\<phi>\<close>)
  case True_ltl
  {
    case 1
    then show \<open>?case\<close> by simp
  next
    case 2
    then show \<open>?case\<close> by (simp, transfer, simp add: prepend'_def)
  }
next
  case (Not_ltl \<phi>)
  {
    case 1
    then show \<open>?case\<close> using Not_ltl by simp
  next
    case 2
    then show \<open>?case\<close> using Not_ltl by simp
  }
next
  case (Prop_ltl x)
  {
    case 1
    then show \<open>?case\<close>
      by (simp, transfer, auto simp: prepend'_def intro: dprefixes_mono[THEN subsetD, rotated])
  next
    case 2
    then show \<open>?case\<close> 
      by (simp, transfer, auto simp: prepend'_def intro: dprefixes_mono[THEN subsetD, rotated])
  }
next
  case (Or_ltl \<phi>1 \<phi>2)
  {
    case 1
    then show \<open>?case\<close>
      apply (simp add: prepend_Union[THEN sym])
      using Or_ltl(1, 3)
      by (metis (no_types, lifting) dset.inf_sup_distrib2 dset.sup_mono)
  next
    case 2
    then show \<open>?case\<close>
      apply (simp add: prepend_Inter[THEN sym])
      using Or_ltl(2,4)
      by (meson dset.dual_order.refl dset.dual_order.trans dset.inf.coboundedI2
                dset.inf_le1 dset.inf_mono)
  }
next
  case (And_ltl \<phi>1 \<phi>2)
  {
    case 1
    then show \<open>?case\<close>
      apply (simp add: prepend_Inter[THEN sym])
      using And_ltl(1,3)
      by (meson dset.dual_order.trans dset.inf_le1 dset.inf_le2 dset.le_infI)
  next
    case 2
    then show \<open>?case\<close>
      apply (simp add: prepend_Union[THEN sym])
      using And_ltl(2, 4)
      by (metis (no_types, lifting) dset.inf_sup_distrib2 dset.sup_mono)
  }
next
  case (Next_ltl \<phi>)
  {
    case 1
    then show \<open>?case\<close> by simp
  next
    case 2
    then show \<open>?case\<close> by simp
  }
next
  case (Until_ltl \<phi>1 \<phi>2)
  {
    case 1
    then show \<open>?case\<close> (* TODO tidy*)
      apply (simp only: progress.simps)
      apply (simp add: prepend_Union[THEN sym] prepend_Inter[THEN sym])
       apply (subst dset.inf_commute)
      apply (subst dset.distrib(3))
      apply (rule dset.order_trans)
       apply (rule dset.sup_mono[OF _ dset.order_refl])
      apply (subst dset.inf_commute)
       apply (rule Until_ltl(3))
      apply (subst dset.inf_assoc[THEN sym])
      apply (rule dset.order_trans)
       apply (rule dset.sup_mono[OF dset.order_refl])
       apply (rule dset.inf_mono[OF _ dset.order_refl])
       apply (subst dset.inf_commute)
       apply (rule Until_ltl(1))
      apply (subst iterate_unroll_Union[OF until_cont], simp)
      by (simp add: dset.inf.commute prepend_Union)
  next
    case 2
    then show \<open>?case\<close>
      apply simp
      apply (subst prepend_Inter[THEN sym] prepend_Union[THEN sym], simp)
      apply (subst dset.inf_commute)
      apply (subst inf_inf)
      apply (rule dset.order_trans)
       apply (rule dset.inf_mono)
        apply (subst dset.inf_commute)
        apply (rule Until_ltl(4))
      apply (simp add: prepend_Union[THEN sym])
      apply (subst dset.distrib(3))
       apply (rule dset.sup_mono)
      apply (subst dset.inf_commute)
        apply (rule Until_ltl(2))
       apply (rule dset.le_infI2, rule dset.order_refl)
      apply (subst iterate_unroll_Inter[OF release_cont,simplified]; simp) 
      by (metis dset.inf_le2 dset.sup.commute)
  }
qed

theorem progression_tf' :
  \<open>\<lbrakk> \<phi> \<rbrakk>\<^sub>3 T \<sqinter> compr (\<lambda>t. t \<noteq> \<epsilon> \<and> thead t = \<sigma>) \<sqsubseteq> prepend (\<lbrakk>progress \<phi> \<sigma> \<rbrakk>\<^sub>3 T) \<close>
  \<open>\<lbrakk> \<phi> \<rbrakk>\<^sub>3 F \<sqinter> compr (\<lambda>t. t \<noteq> \<epsilon> \<and> thead t = \<sigma>) \<sqsubseteq> prepend (\<lbrakk>progress \<phi> \<sigma> \<rbrakk>\<^sub>3 F) \<close>
proof (induct \<open>\<phi>\<close>)
  case True_ltl
  {
    case 1
    then show \<open>?case\<close> by (simp, transfer, simp add: prepend'_def)
  next
    case 2
    then show \<open>?case\<close> by simp
  }
next
  case (Not_ltl \<phi>)
  {
    case 1
    then show \<open>?case\<close> using Not_ltl by simp
  next
    case 2
    then show \<open>?case\<close> using Not_ltl by simp
  }
next
  case (Prop_ltl x)
  {
    case 1
    then show \<open>?case\<close> apply simp
      apply transfer
      apply clarsimp
      apply (clarsimp simp: prepend'_def)
      apply (subst compr'_inter_thead)
      by (metis (mono_tags, lifting) Collect_empty_eq dprefixes_empty)
  next
    case 2
    then show \<open>?case\<close> 
      apply simp
      apply transfer
      apply (clarsimp simp: prepend'_def)
      apply (subst compr'_inter_thead)
      by (metis (mono_tags, lifting) Collect_empty_eq dprefixes_empty)
  }
next
  case (Or_ltl \<phi>1 \<phi>2)
  {
    case 1
    then show \<open>?case\<close>
      apply (simp add: prepend_Union[THEN sym])
      using Or_ltl(1,3)
      by (metis (no_types, lifting) dset.inf_sup_distrib2 dset.sup_mono)
  next
    case 2
    then show \<open>?case\<close>
      apply (simp add: prepend_Inter[THEN sym])
      using Or_ltl(2,4)
      by (meson dset.dual_order.refl dset.dual_order.trans dset.inf.coboundedI2 dset.inf_le1 dset.inf_mono)
  }
next
  case (And_ltl \<phi>1 \<phi>2)
  {
    case 1
    then show \<open>?case\<close> 
      apply (simp add: prepend_Inter[THEN sym])
      using And_ltl(1,3)
      by (meson dset.dual_order.refl dset.dual_order.trans dset.le_inf_iff)
  next
    case 2
    then show \<open>?case\<close> 
      apply (simp add: prepend_Union[THEN sym])
      using And_ltl(2,4)
      by (metis (no_types,lifting) dset.inf_sup_distrib2 dset.sup_mono)
  }
next
  case (Next_ltl \<phi>)
  {
    case 1
    then show \<open>?case\<close> using Next_ltl by simp
  next
    case 2
    then show \<open>?case\<close> using Next_ltl by simp
  }
next
  case (Until_ltl \<phi>1 \<phi>2)
  {
    case 1
    then show \<open>?case\<close>
    unfolding ltl_semantics\<^sub>3.simps u\<^sub>3_operator.simps
              ltl_semantics.simps progress.simps u_operator.simps or_AiF\<^sub>3.simps and_AiF\<^sub>3.simps
      apply (simp add: full_SetCompr_eq prepend_Union[THEN sym])
      apply (rule dset.order_trans[rotated])
       apply (rule dset.sup_mono [OF _ dset.order_refl], rule Until_ltl(3))
      apply (simp add: prepend_Inter[THEN sym])
      apply (rule dset.order_trans[rotated])
       apply (rule dset.sup_mono [OF dset.order_refl])
       apply (rule dset.inf_mono [OF _ dset.order_refl])
     apply (rule Until_ltl(1))
    apply (subst iterate_unroll_Union[OF until_cont], simp)
    apply (subst dset.inf_commute)
    apply (subst dset.inf_sup_distrib1)
    apply (simp, rule conjI)
     apply (subst dset.inf_commute)
     apply auto[1]
    by (meson dset.eq_refl dset.inf.boundedI dset.le_infE dset.le_supI2)
  next
    case 2
    then show \<open>?case\<close>
    unfolding ltl_semantics\<^sub>3.simps u\<^sub>3_operator.simps
              ltl_semantics.simps progress.simps u_operator.simps or_AiF\<^sub>3.simps and_AiF\<^sub>3.simps
      apply (simp add: full_SetCompr_eq prepend_Inter[THEN sym])
      apply (rule conjI,rule dset.order_trans[rotated])
        apply (rule Until_ltl(4))
       apply (rule dset.inf_mono; simp?)
       apply (metis iterate.simps(1) dset.Inf_lower rangeI)
      apply (simp add: prepend_Union[THEN sym])
      apply (rule dset.order_trans[rotated])
       apply (rule dset.sup_mono)
        apply (rule Until_ltl(2))
     apply (rule dset.order_refl)
    apply (subst iterate_unroll_Inter[OF release_cont], simp)
    apply (simp add: prepend_Inter[THEN sym] image_image)
    apply (subst dset.inf_assoc)
    apply (subst dset.sup_inf_distrib2)
    apply (rule dset.le_infI2)
    by (simp add: dset.inf.coboundedI1 insert_commute)
  }
qed

theorem progression_tf'_u:
  shows \<open>\<lbrakk> \<phi> \<rbrakk>\<^sub>3 A \<sqinter> compr (\<lambda>t. t \<noteq> \<epsilon> \<and> thead t = \<sigma>) \<sqsubseteq> prepend (\<lbrakk>progress \<phi> \<sigma> \<rbrakk>\<^sub>3 A)\<close>
  by (cases \<open>A\<close>; simp add: progression_tf')

theorem progression_tf_u:
  shows \<open>prepend (\<lbrakk>progress \<phi> \<sigma> \<rbrakk>\<^sub>3 A) \<sqinter> compr (\<lambda>t. t \<noteq> \<epsilon> \<and> thead t = \<sigma>) \<sqsubseteq> \<lbrakk> \<phi> \<rbrakk>\<^sub>3 A\<close>
  by (cases \<open>A\<close>; simp add: progression_tf)

lemma fp_compr_helper: \<open>in_dset (Finite (a # t)) (compr (\<lambda> x. x \<noteq> \<epsilon> \<and> thead x = a))\<close>
  apply transfer
  apply (simp add: dprefixes_def subset_iff extensions_def prefix_closure_def prefixes_def)
  by (metis \<epsilon>_def list.distinct(1) nth_Cons_0 thead.simps(1) thead_append trace.inject(1) 
            trace.left_neutral trace.right_neutral)


theorem fp:
shows \<open>in_dset (Finite t) (\<lbrakk> \<phi> \<rbrakk>\<^sub>3 A) \<longleftrightarrow> \<lbrakk> foldl progress \<phi> t \<rbrakk>\<^sub>3 A = \<Sigma>\<infinity> \<close>
proof (induct \<open>t\<close> arbitrary: \<open>\<phi>\<close>)
  case Nil
  then show \<open>?case\<close> 
    by (rule iffI; simp add: in_dset_\<epsilon>[simplified \<epsilon>_def] in_dset_UNIV)
next
  case (Cons a t)
  show \<open>?case\<close>
  proof (simp add: Cons[where \<phi>=\<open>progress \<phi> a\<close>, THEN sym], rule)
    assume \<open>in_dset (Finite (a # t)) (\<lbrakk>\<phi>\<rbrakk>\<^sub>3 A)\<close>
    then show \<open>in_dset (Finite t) (\<lbrakk>progress \<phi> a\<rbrakk>\<^sub>3 A)\<close>
      by (force intro: in_dset_prependD in_dset_subset[OF progression_tf'_u] 
                       in_dset_inter fp_compr_helper)
  next
    assume \<open>in_dset (Finite t) (\<lbrakk>progress \<phi> a\<rbrakk>\<^sub>3 A)\<close>
    then show \<open>in_dset (Finite (a # t)) (\<lbrakk>\<phi>\<rbrakk>\<^sub>3 A)\<close>
      by (force intro: in_dset_subset[OF progression_tf_u] in_dset_inter fp_compr_helper 
                       in_dset_prependI[where x = \<open>Finite u\<close> for u, simplified])
  qed
qed

lemma em_ltl: \<open>\<lbrakk> \<phi> \<rbrakk>\<^sub>l T = UNIV - (\<lbrakk> \<phi> \<rbrakk>\<^sub>l F)\<close>
  by (rule set_eqI; clarsimp simp add: subset_iff ltl_equivalence[THEN sym])

theorem em:
  shows \<open>\<lbrakk> \<phi> \<rbrakk>\<^sub>3 T = complement (\<lbrakk> \<phi> \<rbrakk>\<^sub>3 F)\<close>
  by (force intro: definitives_inverse_eqI simp: ltl3_equiv_ltl em_ltl)

end
