(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header "Additions to RB-Trees"
theory RBT_add
imports RBT
begin
text_raw {*\label{thy:RBT_add}*}

  (* The next two lemmas are in my standard simpset, however I made them 
     explicit for this proof: *)
lemma map_add_dom_app_simps:
  "\<lbrakk> m\<in>dom l2 \<rbrakk> \<Longrightarrow> (l1++l2) m = l2 m"
  "\<lbrakk> m\<notin>dom l1 \<rbrakk> \<Longrightarrow> (l1++l2) m = l2 m" 
  "\<lbrakk> m\<notin>dom l2 \<rbrakk> \<Longrightarrow> (l1++l2) m = l1 m" 
  by (auto simp add: map_add_def split: option.split_asm)

lemma map_add_upd2: "m\<notin>dom e2 \<Longrightarrow> e1(m \<mapsto> u1) ++ e2 = (e1 ++ e2)(m \<mapsto> u1)"
  apply (unfold map_add_def)
  apply (rule ext)
  apply (auto split: option.split)
  done

lemma map_of_alist_of_aux: 
  "st (Tr c t1 k v t2) \<Longrightarrow> RBT.map_of (Tr c t1 k v t2) 
   = RBT.map_of t2 ++ [k\<mapsto>v] ++ RBT.map_of t1"
proof (rule ext)
  fix x
  assume ST: "st (Tr c t1 k v t2)"
  let 
    ?thesis = "RBT.map_of (Tr c t1 k v t2) x 
               = (RBT.map_of t2 ++ [k \<mapsto> v] ++ RBT.map_of t1) x"

  have DOM_T1: "!!k'. k'\<in>dom (RBT.map_of t1) \<Longrightarrow> k>k'" 
  proof -
    fix k'
    from ST have "t1 |\<guillemotleft> k" by simp
    with tlt_prop have "\<forall>k'\<in>keys t1. k>k'" by auto
    moreover assume "k'\<in>dom (RBT.map_of t1)"
    ultimately show "k>k'" using RBT.mapof_keys ST by auto
  qed

  have DOM_T2: "!!k'. k'\<in>dom (RBT.map_of t2) \<Longrightarrow> k<k'" 
  proof -
    fix k'
    from ST have "k \<guillemotleft>| t2" by simp
    with tgt_prop have "\<forall>k'\<in>keys t2. k<k'" by auto
    moreover assume "k'\<in>dom (RBT.map_of t2)"
    ultimately show "k<k'" using RBT.mapof_keys ST by auto
  qed

  {
    assume C: "x<k"
    hence "RBT.map_of (Tr c t1 k v t2) x = RBT.map_of t1 x" by simp
    moreover from C have "x\<notin>dom [k\<mapsto>v]" by simp
    moreover have "x\<notin>dom (RBT.map_of t2)" proof
      assume "x\<in>dom (RBT.map_of t2)"
      with DOM_T2 have "k<x" by blast
      with C show False by simp
    qed
    ultimately have ?thesis by (simp add: map_add_upd2 map_add_dom_app_simps)
  } moreover {
    assume [simp]: "x=k"
    hence "RBT.map_of (Tr c t1 k v t2) x = [k \<mapsto> v] x" by simp
    moreover have "x\<notin>dom (RBT.map_of t1)" proof
      assume "x\<in>dom (RBT.map_of t1)"
      with DOM_T1 have "k>x" by blast
      thus False by simp
    qed
    ultimately have ?thesis by (simp add: map_add_upd2 map_add_dom_app_simps)
  } moreover {
    assume C: "x>k"
    hence "RBT.map_of (Tr c t1 k v t2) x = RBT.map_of t2 x" 
      by (simp add: less_not_sym[of k x])
    moreover from C have "x\<notin>dom [k\<mapsto>v]" by simp
    moreover have "x\<notin>dom (RBT.map_of t1)" proof
      assume "x\<in>dom (RBT.map_of t1)"
      with DOM_T1 have "k>x" by simp
      with C show False by simp
    qed
    ultimately have ?thesis by (simp add: map_add_upd2 map_add_dom_app_simps)
  } ultimately show ?thesis using less_linear by blast
qed  

(* This one is marked with an oops in RBT.thy *)
lemma map_of_alist_of:
  shows "st t \<Longrightarrow> Map.map_of (alist_of t) = map_of t"
proof (induct t)
  case Empty thus ?case by (simp add: RBT.map_of_Empty)
next
  case (Tr c t1 k v t2)
  hence "Map.map_of (alist_of (Tr c t1 k v t2)) 
         = RBT.map_of t2 ++ [k \<mapsto> v] ++ RBT.map_of t1" by simp
  also note map_of_alist_of_aux[OF Tr.prems,symmetric]
  finally show ?case .
qed

lemma tlt_trans: "\<lbrakk>l |\<guillemotleft> u; u\<le>v\<rbrakk> \<Longrightarrow> l |\<guillemotleft> v"
  by (induct l) auto

lemma trt_trans: "\<lbrakk> u\<le>v; v\<guillemotleft>|r \<rbrakk> \<Longrightarrow> u\<guillemotleft>|r"
  by (induct r) auto

lemmas tlt_trans' = tlt_trans[OF _ less_imp_le]
lemmas trt_trans' = trt_trans[OF less_imp_le]


lemma map_of_rbt_finite[simp, intro!]: "finite (dom (RBT.map_of t))"
proof (induct t)
  case Empty thus ?case by simp
next
  case (Tr color t1 a b t2)
  thus ?case
    apply (rule_tac 
      B="insert a (dom (RBT.map_of t1) \<union> dom (RBT.map_of t2))" 
      in finite_subset)
    apply (auto split: split_if_asm)
    done

qed

lemma rbt_dom_node: 
  "st (Tr c t1 k v t2) \<Longrightarrow> 
    dom (RBT.map_of (Tr c t1 k v t2)) 
    = insert k (dom (RBT.map_of t1) \<union> dom (RBT.map_of t2))"
proof -
  assume ST: "st (Tr c t1 k v t2)"
  hence STT[simp]: "st t1" "st t2" by simp_all
  note [simp] = RBT.mapof_keys[OF ST] RBT.mapof_keys[OF STT(1)] 
    RBT.mapof_keys[OF STT(2)]
  thus ?thesis by simp
qed


(* Hide auxiliary lemmas *)
hide (open) fact map_add_dom_app_simps map_add_upd2

end
