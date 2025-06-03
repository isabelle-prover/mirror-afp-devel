theory IsaFoR_Ground_Context
  imports 
    Generic_Context 
    IsaFoR_Ground_Term
begin

abbreviation hole_position where 
  "hole_position \<equiv> hole_pos"

type_synonym 'f ground_context = "('f, 'f ground_term) actxt"

abbreviation apply_ground_context (\<open>_\<langle>_\<rangle>\<^sub>G\<close> [1000, 0] 1000) where
  "C\<langle>s\<rangle>\<^sub>G \<equiv> GFun\<langle>C;s\<rangle>"

interpretation ground_context: "context" where
  hole = \<box> and 
  apply_context = apply_ground_context and 
  compose_context = actxt_compose
proof unfold_locales
  fix c :: "'f ground_context" and t t' 
  assume "c\<langle>t\<rangle>\<^sub>G = c\<langle>t'\<rangle>\<^sub>G" 

  then show "t = t'"
    by (induction c) auto
qed (simp_all add: intp_actxt_compose)

lemma gsubt_at_hole [simp]: "c\<langle>t\<rangle>\<^sub>G !\<^sub>t\<^sub>G hole_position c = t"
  by (induction c) auto

lemma hole_position_in_positions\<^sub>G [intro]: "hole_position c \<in> positions\<^sub>G c\<langle>t\<rangle>\<^sub>G"
  by (induction c) auto

fun context_at_position\<^sub>G :: "'f ground_term \<Rightarrow> pos \<Rightarrow> 'f ground_context" (infixl \<open>!\<^sub>c\<close> 64) where
  "t !\<^sub>c [] = \<box>" |
  "GFun f ts !\<^sub>c i # ps = More f (take i ts) (ts!i !\<^sub>c ps) (drop (Suc i) ts)"

text\<open>Behaves differently than const\<open>replace_gterm_at\<close>!\<close>
abbreviation replace_at\<^sub>G (\<open>_\<lbrakk>_ := _\<rbrakk>\<close> [70, 0, 50] 70) where
  "replace_at\<^sub>G t p s \<equiv> (t !\<^sub>c p)\<langle>s\<rangle>\<^sub>G"

lemma replace_at\<^sub>G_hole [simp]: "c\<langle>t\<rangle>\<^sub>G\<lbrakk>hole_position c := t'\<rbrakk> = c\<langle>t'\<rangle>\<^sub>G"
  by (induction c) auto

lemma gsubt_at_id: 
  assumes "p \<in> positions\<^sub>G t"  
  shows "t\<lbrakk>p := t !\<^sub>t\<^sub>G p\<rbrakk> = t"
  using assms 
  by (induction t arbitrary: p) (auto simp: id_take_nth_drop[symmetric])

(* TODO: actually not needed here, use me to clean up nonground case *)
lemma parallel_replace_at\<^sub>G_in_positions\<^sub>G:
  assumes "p\<^sub>1 \<bottom> p\<^sub>2" "p\<^sub>1 \<in> positions\<^sub>G t" 
  shows "p\<^sub>2 \<in> positions\<^sub>G (t\<lbrakk>p\<^sub>1 := t'\<rbrakk>) \<longleftrightarrow> p\<^sub>2 \<in> positions\<^sub>G t"
proof (induction rule: parallel_induct_first_in_positions\<^sub>G[OF assms])
  case base: (1 p\<^sub>1 p\<^sub>2 i j q\<^sub>1 q\<^sub>2 t f ts)

  let ?p\<^sub>1 = "i # q\<^sub>1"
  let ?t\<^sub>i = "(ts ! i)\<lbrakk>q\<^sub>1 := t'\<rbrakk>"

  have "t\<lbrakk>?p\<^sub>1 := t'\<rbrakk> = GFun f (ts[i := ?t\<^sub>i])"
    unfolding base upd_conv_take_nth_drop[OF base(5)] 
    by simp

  then show ?case 
    unfolding base
    using base
    by auto
next
  case step: (2 p\<^sub>1 p\<^sub>2 p k i j q\<^sub>1 q\<^sub>2 t f ts)

  then have "min (length ts) k = k" 
    by simp

  then show ?case
    using step
    by (auto simp: nth_append)
qed

(* TODO: actually not needed here, use me to clean up nonground case *)
lemma parallel_replace_at\<^sub>G_gsubt_at: 
  assumes "p\<^sub>1 \<bottom> p\<^sub>2" "p\<^sub>1 \<in> positions\<^sub>G t"
  shows "t\<lbrakk>p\<^sub>1 := t'\<rbrakk> !\<^sub>t\<^sub>G p\<^sub>2 = t !\<^sub>t\<^sub>G p\<^sub>2"
proof (induction rule: parallel_induct_first_in_positions\<^sub>G[OF assms])
  case base: (1 p\<^sub>1 p\<^sub>2 i j q\<^sub>1 q\<^sub>2 t f ts)

  let ?p\<^sub>1 = "i # q\<^sub>1"
  let ?p\<^sub>2 = "j # q\<^sub>2"

  let ?t\<^sub>i = "replace_at\<^sub>G (ts ! i) q\<^sub>1 t'"
  let ?ts\<^sub>i = "ts[i := ?t\<^sub>i]"

  have "t\<lbrakk>?p\<^sub>1 := t'\<rbrakk> !\<^sub>t\<^sub>G ?p\<^sub>2 = GFun f ?ts\<^sub>i !\<^sub>t\<^sub>G ?p\<^sub>2"
    unfolding base upd_conv_take_nth_drop[OF base(5)] 
    by simp

  also have "... = ts ! j !\<^sub>t\<^sub>G q\<^sub>2"
    using base 
    by simp

  finally show ?case
    by (simp add: base.hyps)
next
  case step: (2 p\<^sub>1 p\<^sub>2 p k i j q\<^sub>1 q\<^sub>2 t f ts)
 
  then show ?case
    by (simp add: nth_append)
qed

lemma parallel_replace_at\<^sub>G:
  assumes "p\<^sub>1 \<bottom> p\<^sub>2"  "p\<^sub>1 \<in> positions\<^sub>G t" "p\<^sub>2 \<in> positions\<^sub>G t"
  shows "t\<lbrakk>p\<^sub>1 := s\<^sub>1\<rbrakk>\<lbrakk>p\<^sub>2 := s\<^sub>2\<rbrakk> = t\<lbrakk>p\<^sub>2 := s\<^sub>2\<rbrakk>\<lbrakk>p\<^sub>1 := s\<^sub>1\<rbrakk>"
proof (induction rule: parallel_induct_in_positions\<^sub>G[OF assms])
  case base: (1 p\<^sub>1 p\<^sub>2 i j q\<^sub>1 q\<^sub>2 t f ts)

  let ?p\<^sub>1 = "i # q\<^sub>1"
  let ?p\<^sub>2 = "j # q\<^sub>2"
  let ?s\<^sub>1 = "(ts ! i)\<lbrakk>q\<^sub>1 := s\<^sub>1\<rbrakk>"
  let ?s\<^sub>2 = "(ts ! j)\<lbrakk>q\<^sub>2 := s\<^sub>2\<rbrakk>"
  let ?ts\<^sub>1 = "ts[i := ?s\<^sub>1]"
  let ?ts\<^sub>2 = "ts[j := ?s\<^sub>2]"

  note i_neq_j = base(3)

  note i = base(6)
  note j = base(5)

  have j': "j < length ?ts\<^sub>1" and i': "i < length ?ts\<^sub>2" 
    using i j
    by simp_all

  have "t\<lbrakk>?p\<^sub>1 := s\<^sub>1\<rbrakk>\<lbrakk>?p\<^sub>2 := s\<^sub>2\<rbrakk> = (GFun f ?ts\<^sub>1)\<lbrakk>?p\<^sub>2 := s\<^sub>2\<rbrakk>" 
    unfolding base upd_conv_take_nth_drop[OF i] 
    by simp

  also have "... = GFun f (?ts\<^sub>1[j := ?s\<^sub>2])"
    unfolding upd_conv_take_nth_drop[OF j']
    using i_neq_j
    by simp

  also have "... = GFun f (?ts\<^sub>2[i := ?s\<^sub>1])"
    using list_update_swap[OF i_neq_j]
    by simp

  also have "... = (GFun f ?ts\<^sub>2)\<lbrakk>?p\<^sub>1 := s\<^sub>1\<rbrakk>"
    unfolding upd_conv_take_nth_drop[OF i'] 
    using i_neq_j
    by simp

  also have "... = t\<lbrakk>?p\<^sub>2 := s\<^sub>2\<rbrakk>\<lbrakk>?p\<^sub>1 := s\<^sub>1\<rbrakk>" 
    unfolding upd_conv_take_nth_drop[OF j] base
    by simp

  finally show ?case
    unfolding base
    by satx
next
  case step: 2

  then show ?case 
    by (simp add: nth_append)
qed

end
