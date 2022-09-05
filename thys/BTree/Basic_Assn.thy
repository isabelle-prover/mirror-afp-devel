theory Basic_Assn
  imports
    "Refine_Imperative_HOL.Sepref_HOL_Bindings"
    "Refine_Imperative_HOL.Sepref_Basic"
begin

section "Auxilary imperative assumptions"

text "The following auxiliary assertion types and lemmas were provided by Peter Lammich"

subsection \<open>List-Assn\<close>



lemma list_assn_cong[fundef_cong]:
  "\<lbrakk> xs=xs'; ys=ys'; \<And>x y. \<lbrakk> x\<in>set xs; y\<in>set ys \<rbrakk> \<Longrightarrow> A x y = A' x y \<rbrakk> \<Longrightarrow> list_assn A xs ys = list_assn A' xs' ys'"
  by (induction xs ys arbitrary: xs' ys' rule: list_assn.induct) auto


lemma list_assn_app_one: "list_assn P (l1@[x]) (l1'@[y]) = list_assn P l1 l1' * P x y"
  by simp

(* ------------------ ADDED by NM in course of btree_imp -------- *)


lemma list_assn_len: "h \<Turnstile> list_assn A xs ys \<Longrightarrow> length xs = length ys"
  using list_assn_aux_ineq_len by fastforce


lemma list_assn_append_Cons_left: "list_assn A (xs@x#ys) zs = (\<exists>\<^sub>A zs1 z zs2. list_assn A xs zs1 * A x z * list_assn A ys zs2 * \<up>(zs1@z#zs2 = zs))"
  by (sep_auto simp add: list_assn_aux_cons_conv list_assn_aux_append_conv1 intro!: ent_iffI)


lemma list_assn_aux_append_Cons: 
  shows "length xs = length zsl \<Longrightarrow> list_assn A (xs@x#ys) (zsl@z#zsr) = (list_assn A xs zsl * A x z * list_assn A ys zsr) "
  by (sep_auto simp add: mult.assoc)

lemma list_assn_prod_split: "list_assn (\<lambda>x y. P x y * Q x y) as bs = list_assn P as bs * list_assn Q as bs"
proof(cases "length as = length bs")
  case True
  then show ?thesis
  proof (induction rule: list_induct2)
    case Nil
    then show ?case by sep_auto
  next
    case (Cons x xs y ys)
    show ?case
    proof (rule ent_iffI, goal_cases)
      case 1
      then show ?case
      using Cons by sep_auto
    next
      case 2
      then show ?case
      using Cons by sep_auto
    qed
  qed
next
  case False
  then show ?thesis
    by (simp add: list_assn_aux_ineq_len)
qed

(* -------------------------------------------- *)

subsection \<open>Prod-Assn\<close>


lemma prod_assn_cong[fundef_cong]:
  "\<lbrakk> p=p'; pi=pi'; A (fst p) (fst pi) = A' (fst p) (fst pi); B (snd p) (snd pi) = B' (snd p) (snd pi) \<rbrakk> 
    \<Longrightarrow> (A\<times>\<^sub>aB) p pi = (A'\<times>\<^sub>aB') p' pi'" 
  apply (cases p; cases pi)
  by auto

subsection \<open>Assertions and Magic Wand\<close>

lemma entails_preI: "(\<And>h. h \<Turnstile> P \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q) \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q"
  unfolding entails_def
  by auto

lemma ent_true_drop_true: 
  "P*true\<Longrightarrow>\<^sub>AQ*true \<Longrightarrow> P*R*true\<Longrightarrow>\<^sub>AQ*true"
  using assn_aci(10) ent_true_drop(1) by presburger

(* TODO *)
lemma rem_true: "P*true \<Longrightarrow>\<^sub>A Q*true \<Longrightarrow> P \<Longrightarrow>\<^sub>AQ*true"
  using enttD enttI_true by blast

lemma assn_eq_split:
  assumes "B = C"
  shows "B \<Longrightarrow>\<^sub>A C"
  and "C \<Longrightarrow>\<^sub>A B"
  by (simp_all add: assms)

lemma ent_ex_inst: "\<exists>\<^sub>Ax. P x \<Longrightarrow>\<^sub>A Q \<Longrightarrow> P y \<Longrightarrow>\<^sub>A Q"
  using ent_trans by blast

lemma ent_ex_inst2: "\<exists>\<^sub>Ax y. P x y \<Longrightarrow>\<^sub>A Q \<Longrightarrow> P x y \<Longrightarrow>\<^sub>A Q"
  using ent_trans by blast

lemma ent_wandI2:
  assumes IMP: "P \<Longrightarrow>\<^sub>A (Q -* R)"
  shows "Q*P \<Longrightarrow>\<^sub>A R"
  using assms
  unfolding entails_def 
(*  by (meson assms ent_fwd ent_mp ent_refl fr_rot mod_frame_fwd)*)
proof (clarsimp, goal_cases)
  case (1 h as)
  then obtain as1 as2 where "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "(h,as1) \<Turnstile> Q" "(h,as2) \<Turnstile> P"
    by (metis mod_star_conv prod.inject)
  then have "(h,as2) \<Turnstile> (Q-*R)"
    by (simp add: "1"(1))
  then have "(h,as1\<union>as2) \<Turnstile> Q * (Q-*R)"
    by (simp add: \<open>(h, as1) \<Turnstile> Q\<close> \<open>as1 \<inter> as2 = {}\<close> star_assnI)
  then show ?case 
    using \<open>as = as1 \<union> as2\<close> ent_fwd ent_mp by blast
qed

lemma ent_wand: "(P \<Longrightarrow>\<^sub>A (Q -* R)) = (Q*P \<Longrightarrow>\<^sub>A R)"
  using ent_wandI2 ent_wandI by blast

lemma wand_ent_trans:
  assumes "P' \<Longrightarrow>\<^sub>A P"
      and "Q \<Longrightarrow>\<^sub>A Q'"
    shows "P -* Q \<Longrightarrow>\<^sub>A P' -* Q'"
  by (meson assms(1) assms(2) ent_wand ent_frame_fwd ent_refl ent_trans)

lemma wand_elim: "(P -* Q) * (Q -* R) \<Longrightarrow>\<^sub>A (P -* R)"
  by (metis ent_wand ent_frame_fwd ent_mp ent_refl star_assoc)

lemma emp_wand_same: "emp \<Longrightarrow>\<^sub>A (H -* H)"
  by (simp add: ent_wandI)

lemma emp_wand_equal: "(emp -* H) = H"
  apply(intro ent_iffI)
  apply (metis ent_mp norm_assertion_simps(1))
  by (simp add: ent_wandI)

lemma pure_wand_equal: "P \<Longrightarrow> (\<up>(P) -* H) = H"
  by (simp add: emp_wand_equal)

lemma pure_wand_ent: "(P \<Longrightarrow> (H1 \<Longrightarrow>\<^sub>A H2)) \<Longrightarrow> H1 \<Longrightarrow>\<^sub>A \<up>(P) -* H2"
  by (simp add: ent_wand)

lemma "\<up>(P \<longrightarrow> Q) \<Longrightarrow>\<^sub>A (\<up>(P) -* \<up>(Q))"
  by (simp add: pure_wand_ent)

lemma wand_uncurry: "(P*Q) -* R \<Longrightarrow>\<^sub>A P -* (Q -* R)"
  by (simp add: assn_aci ent_mp ent_wandI fr_rot)

lemma wand_absorb: "(P -* Q) * R \<Longrightarrow>\<^sub>A (P -* (Q * R))"
  by (smt (z3) ent_mp ent_refl ent_star_mono ent_wandI star_aci(2) star_aci(3))

lemma wand_ent_self: "P \<Longrightarrow>\<^sub>A Q -* (Q * P)"
  by (simp add: ent_wandI)

lemma wand_ent_cancel: "P * ((P * Q) -* R) \<Longrightarrow>\<^sub>A Q -* R"
  by (simp add: ent_wandI2 wand_uncurry)


lemma "\<exists>R. Q * R \<Longrightarrow>\<^sub>A P"
  using ent_mp by auto

lemma "P \<Longrightarrow>\<^sub>A Q * true \<Longrightarrow> P = Q * (Q -* P)"
  apply(intro ent_iffI)
proof(goal_cases)
  case 2
  then show ?case
    by (simp add: ent_mp)
next
  case test: 1
  show ?case
    unfolding entails_def
    apply clarsimp
  proof (goal_cases)
    case (1 a b)
    then have "(a,b) \<Turnstile> Q * true"
      using test entails_def
      by blast
    then obtain h as1 as2 where *:
        "(a,b) = (h, as1 \<union> as2) \<and> as1 \<inter> as2 = {} \<and> (h, as1) \<Turnstile> Q \<and> (h, as2) \<Turnstile> true"
    using mod_star_conv by auto
  then have "(h, as1 \<union> as2) \<Turnstile> P" "(a,b) = (h, as1 \<union> as2)" 
    using "1" by blast+
  then show ?case 
    apply simp
    thm star_assnI
    apply(intro star_assnI)
    apply (simp_all add: *)
    apply(intro wand_assnI)
    apply (meson "*" models_in_range)
    apply auto
    oops

end