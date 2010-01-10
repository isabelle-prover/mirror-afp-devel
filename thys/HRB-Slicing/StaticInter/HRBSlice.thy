header {* \isaheader{Horwitz-Reps-Binkley Slice} *}

theory HRBSlice imports SDG begin

context SDG begin

subsection {* Set describing phase 1 of the two-phase slicer *}

inductive_set sum_SDG_slice1 :: "'node SDG_node \<Rightarrow> 'node SDG_node set"
  for n::"'node SDG_node"
  where refl_slice1:"valid_SDG_node n \<Longrightarrow> n \<in> sum_SDG_slice1 n"
  | cdep_slice1:
  "\<lbrakk>n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'; n' \<in> sum_SDG_slice1 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice1 n"
  | ddep_slice1: 
  "\<lbrakk>n'' s-V\<rightarrow>\<^bsub>dd\<^esub> n'; n' \<in> sum_SDG_slice1 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice1 n"
  | call_slice1:
  "\<lbrakk>n'' s-p\<rightarrow>\<^bsub>call\<^esub> n'; n' \<in> sum_SDG_slice1 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice1 n"
  | param_in_slice1: 
  "\<lbrakk>n'' s-p:V\<rightarrow>\<^bsub>in\<^esub> n'; n' \<in> sum_SDG_slice1 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice1 n"
  | sum_slice1:
  "\<lbrakk>n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'; n' \<in> sum_SDG_slice1 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice1 n"


lemma slice1_cdep_slice1:
  "\<lbrakk>nx \<in> sum_SDG_slice1 n; n s\<longrightarrow>\<^bsub>cd\<^esub> n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice1 n'"
by(induct rule:sum_SDG_slice1.induct,
   auto intro:sum_SDG_slice1.intros sum_SDG_edge_valid_SDG_node)

lemma slice1_ddep_slice1:
  "\<lbrakk>nx \<in> sum_SDG_slice1 n; n s-V\<rightarrow>\<^bsub>dd\<^esub> n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice1 n'"
by(induct rule:sum_SDG_slice1.induct,
   auto intro:sum_SDG_slice1.intros sum_SDG_edge_valid_SDG_node)

lemma slice1_sum_slice1:
  "\<lbrakk>nx \<in> sum_SDG_slice1 n; n s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice1 n'"
by(induct rule:sum_SDG_slice1.induct,
   auto intro:sum_SDG_slice1.intros sum_SDG_edge_valid_SDG_node)

lemma slice1_call_slice1:
  "\<lbrakk>nx \<in> sum_SDG_slice1 n; n s-p\<rightarrow>\<^bsub>call\<^esub> n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice1 n'"
by(induct rule:sum_SDG_slice1.induct,
   auto intro:sum_SDG_slice1.intros sum_SDG_edge_valid_SDG_node)

lemma slice1_param_in_slice1:
  "\<lbrakk>nx \<in> sum_SDG_slice1 n; n s-p:V\<rightarrow>\<^bsub>in\<^esub> n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice1 n'"
by(induct rule:sum_SDG_slice1.induct,
   auto intro:sum_SDG_slice1.intros sum_SDG_edge_valid_SDG_node)


lemma is_SDG_path_slice1:
  "\<lbrakk>n is-ns\<rightarrow>\<^isub>d* n'; n' \<in> sum_SDG_slice1 n''\<rbrakk> \<Longrightarrow> n \<in> sum_SDG_slice1 n''"
proof(induct rule:intra_sum_SDG_path.induct)
  case isSp_Nil thus ?case by simp
next
  case (isSp_Append_cdep n ns nx n')
  note IH = `nx \<in> sum_SDG_slice1 n'' \<Longrightarrow> n \<in> sum_SDG_slice1 n''`
  from `nx s\<longrightarrow>\<^bsub>cd\<^esub> n'` `n' \<in> sum_SDG_slice1 n''`
  have "nx \<in> sum_SDG_slice1 n''" by(rule cdep_slice1)
  from IH[OF this] show ?case .
next
  case (isSp_Append_ddep n ns nx V n')
  note IH = `nx \<in> sum_SDG_slice1 n'' \<Longrightarrow> n \<in> sum_SDG_slice1 n''`
  from `nx s-V\<rightarrow>\<^bsub>dd\<^esub> n'` `n' \<in> sum_SDG_slice1 n''`
  have "nx \<in> sum_SDG_slice1 n''" by(rule ddep_slice1)
  from IH[OF this] show ?case .
next
  case (isSp_Append_sum n ns nx p n')
  note IH = `nx \<in> sum_SDG_slice1 n'' \<Longrightarrow> n \<in> sum_SDG_slice1 n''`
  from `nx s-p\<rightarrow>\<^bsub>sum\<^esub> n'` `n' \<in> sum_SDG_slice1 n''`
  have "nx \<in> sum_SDG_slice1 n''" by(rule sum_slice1)
  from IH[OF this] show ?case .
qed


subsection {* Set describing phase 2 of the two-phase slicer *}

inductive_set sum_SDG_slice2 :: "'node SDG_node \<Rightarrow> 'node SDG_node set"
  for n::"'node SDG_node"
  where refl_slice2:"valid_SDG_node n \<Longrightarrow> n \<in> sum_SDG_slice2 n"
  | cdep_slice2:
  "\<lbrakk>n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'; n' \<in> sum_SDG_slice2 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice2 n"
  | ddep_slice2: 
  "\<lbrakk>n'' s-V\<rightarrow>\<^bsub>dd\<^esub> n'; n' \<in> sum_SDG_slice2 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice2 n"
  | return_slice2:
  "\<lbrakk>n'' s-p\<rightarrow>\<^bsub>ret\<^esub> n'; n' \<in> sum_SDG_slice2 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice2 n"
  | param_out_slice2: 
  "\<lbrakk>n'' s-p:V\<rightarrow>\<^bsub>out\<^esub> n'; n' \<in> sum_SDG_slice2 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice2 n"
  | sum_slice2:
  "\<lbrakk>n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'; n' \<in> sum_SDG_slice2 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice2 n"


lemma slice2_cdep_slice2:
  "\<lbrakk>nx \<in> sum_SDG_slice2 n; n s\<longrightarrow>\<^bsub>cd\<^esub> n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice2 n'"
by(induct rule:sum_SDG_slice2.induct,
   auto intro:sum_SDG_slice2.intros sum_SDG_edge_valid_SDG_node)

lemma slice2_ddep_slice2:
  "\<lbrakk>nx \<in> sum_SDG_slice2 n; n s-V\<rightarrow>\<^bsub>dd\<^esub> n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice2 n'"
by(induct rule:sum_SDG_slice2.induct,
   auto intro:sum_SDG_slice2.intros sum_SDG_edge_valid_SDG_node)

lemma slice2_sum_slice2:
  "\<lbrakk>nx \<in> sum_SDG_slice2 n; n s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice2 n'"
by(induct rule:sum_SDG_slice2.induct,
   auto intro:sum_SDG_slice2.intros sum_SDG_edge_valid_SDG_node)

lemma slice2_ret_slice2:
  "\<lbrakk>nx \<in> sum_SDG_slice2 n; n s-p\<rightarrow>\<^bsub>ret\<^esub> n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice2 n'"
by(induct rule:sum_SDG_slice2.induct,
   auto intro:sum_SDG_slice2.intros sum_SDG_edge_valid_SDG_node)

lemma slice2_param_out_slice2:
  "\<lbrakk>nx \<in> sum_SDG_slice2 n; n s-p:V\<rightarrow>\<^bsub>out\<^esub> n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice2 n'"
by(induct rule:sum_SDG_slice2.induct,
   auto intro:sum_SDG_slice2.intros sum_SDG_edge_valid_SDG_node)


lemma is_SDG_path_slice2:
  "\<lbrakk>n is-ns\<rightarrow>\<^isub>d* n'; n' \<in> sum_SDG_slice2 n''\<rbrakk> \<Longrightarrow> n \<in> sum_SDG_slice2 n''"
proof(induct rule:intra_sum_SDG_path.induct)
  case isSp_Nil thus ?case by simp
next
  case (isSp_Append_cdep n ns nx n')
  note IH = `nx \<in> sum_SDG_slice2 n'' \<Longrightarrow> n \<in> sum_SDG_slice2 n''`
  from `nx s\<longrightarrow>\<^bsub>cd\<^esub> n'` `n' \<in> sum_SDG_slice2 n''`
  have "nx \<in> sum_SDG_slice2 n''" by(rule cdep_slice2)
  from IH[OF this] show ?case .
next
  case (isSp_Append_ddep n ns nx V n')
  note IH = `nx \<in> sum_SDG_slice2 n'' \<Longrightarrow> n \<in> sum_SDG_slice2 n''`
  from `nx s-V\<rightarrow>\<^bsub>dd\<^esub> n'` `n' \<in> sum_SDG_slice2 n''`
  have "nx \<in> sum_SDG_slice2 n''" by(rule ddep_slice2)
  from IH[OF this] show ?case .
next
  case (isSp_Append_sum n ns nx p n')
  note IH = `nx \<in> sum_SDG_slice2 n'' \<Longrightarrow> n \<in> sum_SDG_slice2 n''`
  from `nx s-p\<rightarrow>\<^bsub>sum\<^esub> n'` `n' \<in> sum_SDG_slice2 n''`
  have "nx \<in> sum_SDG_slice2 n''" by(rule sum_slice2)
  from IH[OF this] show ?case .
qed



lemma slice2_is_SDG_path_slice2: 
  "\<lbrakk>n is-ns\<rightarrow>\<^isub>d* n'; n'' \<in> sum_SDG_slice2 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice2 n'"
proof(induct rule:intra_sum_SDG_path.induct)
  case isSp_Nil thus ?case by simp
next
  case (isSp_Append_cdep n ns nx n')
  from `n'' \<in> sum_SDG_slice2 n \<Longrightarrow> n'' \<in> sum_SDG_slice2 nx` `n'' \<in> sum_SDG_slice2 n`
  have "n'' \<in> sum_SDG_slice2 nx" .
  with `nx s\<longrightarrow>\<^bsub>cd\<^esub> n'` show ?case by -(rule slice2_cdep_slice2)
next
  case (isSp_Append_ddep n ns nx V n')
  from `n'' \<in> sum_SDG_slice2 n \<Longrightarrow> n'' \<in> sum_SDG_slice2 nx` `n'' \<in> sum_SDG_slice2 n`
  have "n'' \<in> sum_SDG_slice2 nx" .
  with `nx s-V\<rightarrow>\<^bsub>dd\<^esub> n'` show ?case by -(rule slice2_ddep_slice2)
next
  case (isSp_Append_sum n ns nx p n')
  from `n'' \<in> sum_SDG_slice2 n \<Longrightarrow> n'' \<in> sum_SDG_slice2 nx` `n'' \<in> sum_SDG_slice2 n`
  have "n'' \<in> sum_SDG_slice2 nx" .
  with `nx s-p\<rightarrow>\<^bsub>sum\<^esub> n'` show ?case by -(rule slice2_sum_slice2)
qed


subsection {* The backward slice using the Horwitz-Reps-Binkley slicer *}

inductive_set combine_SDG_slices :: "'node SDG_node set \<Rightarrow> 'node SDG_node set"
  for S::"'node SDG_node set"
  where combSlice_refl:"n \<in> S \<Longrightarrow> n \<in> combine_SDG_slices S" 
  | combSlice_Return_parent_node:
  "\<lbrakk>n' \<in> S; n'' s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n'); n \<in> sum_SDG_slice2 n'\<rbrakk> 
  \<Longrightarrow> n \<in> combine_SDG_slices S"


definition HRB_slice :: "'node SDG_node \<Rightarrow> 'node SDG_node set"
  where "HRB_slice n \<equiv> combine_SDG_slices (sum_SDG_slice1 n)"


lemma HRB_slice_refl:
  assumes "valid_node m" shows "CFG_node m \<in> HRB_slice (CFG_node m)"
proof -
  from `valid_node m` have "CFG_node m \<in> sum_SDG_slice1 (CFG_node m)"
    by(fastsimp intro:refl_slice1)
  thus ?thesis by(fastsimp intro:combSlice_refl simp:HRB_slice_def)
qed


lemma HRB_slice_valid_node: 
  assumes "n \<in> HRB_slice n\<^isub>c" shows "valid_SDG_node n"
proof -
  from `n \<in> HRB_slice n\<^isub>c` have "n \<in> combine_SDG_slices (sum_SDG_slice1 n\<^isub>c)"
    by(simp add:HRB_slice_def)
  thus "valid_SDG_node n"
  proof(induct rule:combine_SDG_slices.induct)
    case combSlice_refl
    thus ?case
      by(induct rule:sum_SDG_slice1.induct,auto intro:sum_SDG_edge_valid_SDG_node)
  next
    case (combSlice_Return_parent_node n' n'' p n)
    from `n \<in> sum_SDG_slice2 n'`
    show ?case
      by(induct rule:sum_SDG_slice2.induct,auto intro:sum_SDG_edge_valid_SDG_node)
  qed
qed


lemma valid_SDG_node_in_slice_parent_node_in_slice:
  assumes "n \<in> HRB_slice n\<^isub>c" shows "CFG_node (parent_node n) \<in> HRB_slice n\<^isub>c"
proof -
  from `n \<in> HRB_slice n\<^isub>c` have "valid_SDG_node n" by(rule HRB_slice_valid_node)
  hence "n = CFG_node (parent_node n) \<or> CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n"
    by(rule valid_SDG_node_cases)
  thus ?thesis
  proof
    assume "n = CFG_node (parent_node n)"
    with `n \<in> HRB_slice n\<^isub>c` show ?thesis by simp
  next
    assume "CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n"
    hence "CFG_node (parent_node n) s\<longrightarrow>\<^bsub>cd\<^esub> n" by(rule SDG_edge_sum_SDG_edge)
    with `n \<in> HRB_slice n\<^isub>c` show ?thesis
      by(fastsimp elim:combine_SDG_slices.cases 
	         intro:combine_SDG_slices.intros cdep_slice1 cdep_slice2 
	          simp:HRB_slice_def)
  qed
qed


lemma HRB_slice_is_SDG_path_HRB_slice: 
  "\<lbrakk>n is-ns\<rightarrow>\<^isub>d* n'; n'' \<in> HRB_slice n\<rbrakk> \<Longrightarrow> n'' \<in> HRB_slice n'"
proof(induct rule:intra_sum_SDG_path.induct)
  case isSp_Nil thus ?case by simp
next
  case (isSp_Append_cdep n ns nx n')
  from `n'' \<in> HRB_slice n \<Longrightarrow> n'' \<in> HRB_slice nx` `n'' \<in> HRB_slice n`
  have "n'' \<in> combine_SDG_slices (sum_SDG_slice1 nx)" by(simp add:HRB_slice_def)
  hence "n'' \<in> combine_SDG_slices (sum_SDG_slice1 n')"
  proof(induct rule:combine_SDG_slices.induct)
    case (combSlice_refl n)
    from `n \<in> sum_SDG_slice1 nx` `nx s\<longrightarrow>\<^bsub>cd\<^esub> n'` have "n \<in> sum_SDG_slice1 n'"
      by (rule slice1_cdep_slice1)
    thus ?case by(rule combine_SDG_slices.combSlice_refl)
  next
    case (combSlice_Return_parent_node nx' n'' p n)
    from `nx' \<in> sum_SDG_slice1 nx` `nx s\<longrightarrow>\<^bsub>cd\<^esub> n'`
    have "nx' \<in> sum_SDG_slice1 n'" by (rule slice1_cdep_slice1)
    with `n'' s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node nx')` `n \<in> sum_SDG_slice2 nx'` show ?case
      by -(rule combine_SDG_slices.combSlice_Return_parent_node)
  qed
  thus ?case by(simp add:HRB_slice_def)
next
  case (isSp_Append_ddep n ns nx V n')
  from `n'' \<in> HRB_slice n \<Longrightarrow> n'' \<in> HRB_slice nx` `n'' \<in> HRB_slice n`
  have "n'' \<in> combine_SDG_slices (sum_SDG_slice1 nx)" by(simp add:HRB_slice_def)
  hence "n'' \<in> combine_SDG_slices (sum_SDG_slice1 n')"
  proof(induct rule:combine_SDG_slices.induct)
    case (combSlice_refl n)
    from `n \<in> sum_SDG_slice1 nx` `nx s-V\<rightarrow>\<^bsub>dd\<^esub> n'` have "n \<in> sum_SDG_slice1 n'"
      by (rule slice1_ddep_slice1)
    thus ?case by(rule combine_SDG_slices.combSlice_refl)
  next
    case (combSlice_Return_parent_node nx' n'' p n)
    from `nx' \<in> sum_SDG_slice1 nx` `nx s-V\<rightarrow>\<^bsub>dd\<^esub> n'`
    have "nx' \<in> sum_SDG_slice1 n'" by (rule slice1_ddep_slice1)
    with `n'' s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node nx')` `n \<in> sum_SDG_slice2 nx'` show ?case
      by -(rule combine_SDG_slices.combSlice_Return_parent_node)
  qed
  thus ?case by(simp add:HRB_slice_def)
next
  case (isSp_Append_sum n ns nx p n')
  from `n'' \<in> HRB_slice n \<Longrightarrow> n'' \<in> HRB_slice nx` `n'' \<in> HRB_slice n`
  have "n'' \<in> combine_SDG_slices (sum_SDG_slice1 nx)" by(simp add:HRB_slice_def)
  hence "n'' \<in> combine_SDG_slices (sum_SDG_slice1 n')"
  proof(induct rule:combine_SDG_slices.induct)
    case (combSlice_refl n)
    from `n \<in> sum_SDG_slice1 nx` `nx s-p\<rightarrow>\<^bsub>sum\<^esub> n'` have "n \<in> sum_SDG_slice1 n'"
      by (rule slice1_sum_slice1)
    thus ?case by(rule combine_SDG_slices.combSlice_refl)
  next
    case (combSlice_Return_parent_node nx' n'' p' n)
    from `nx' \<in> sum_SDG_slice1 nx` `nx s-p\<rightarrow>\<^bsub>sum\<^esub> n'`
    have "nx' \<in> sum_SDG_slice1 n'" by (rule slice1_sum_slice1)
    with `n'' s-p'\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node nx')` `n \<in> sum_SDG_slice2 nx'` show ?case
      by -(rule combine_SDG_slices.combSlice_Return_parent_node)
  qed
  thus ?case by(simp add:HRB_slice_def)
qed


lemma call_return_nodes_in_slice:
  assumes "valid_edge a" and "kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f"
  and "valid_edge a'" and "kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'" and "a \<in> get_return_edges a'"
  and "CFG_node (targetnode a) \<in> HRB_slice n\<^isub>c" and "parent_node n\<^isub>c \<noteq> sourcenode a"
  shows "CFG_node (sourcenode a) \<in> HRB_slice n\<^isub>c"
  and "CFG_node (sourcenode a') \<in> HRB_slice n\<^isub>c" 
  and "CFG_node (targetnode a') \<in> HRB_slice n\<^isub>c"
proof -
  from `valid_edge a'` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'` `a \<in> get_return_edges a'`
  have "CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a)"
    by(fastsimp intro:sum_SDG_call_summary_edge)
  with `CFG_node (targetnode a) \<in> HRB_slice n\<^isub>c`
  show "CFG_node (sourcenode a') \<in> HRB_slice n\<^isub>c"
    by(fastsimp elim!:combine_SDG_slices.cases 
                intro:combine_SDG_slices.intros sum_slice1 sum_slice2 
                 simp:HRB_slice_def)
  from `CFG_node (targetnode a) \<in> HRB_slice n\<^isub>c`
  have "CFG_node (targetnode a) \<in> combine_SDG_slices (sum_SDG_slice1 n\<^isub>c)"
    by(simp add:HRB_slice_def)
  thus "CFG_node (sourcenode a) \<in> HRB_slice n\<^isub>c"
  proof(induct "CFG_node (targetnode a)" rule:combine_SDG_slices.induct)
    case combSlice_refl
    from `valid_edge a` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f`
    have "CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (targetnode a)"
      by(fastsimp intro:sum_SDG_return_edge)
    with `valid_edge a` 
    have "CFG_node (sourcenode a) \<in> sum_SDG_slice2 (CFG_node (targetnode a))"
      by(fastsimp intro:sum_SDG_slice2.intros)
    with `CFG_node (targetnode a) \<in> sum_SDG_slice1 n\<^isub>c`
      `CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (targetnode a)`
    show ?case by(fastsimp intro:combSlice_Return_parent_node simp:HRB_slice_def)
  next
    case (combSlice_Return_parent_node n' n'' p')
    from `valid_edge a` `kind a = Q\<^bsub>p\<^esub>\<hookleftarrow>f`
    have "CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (targetnode a)"
      by(fastsimp intro:sum_SDG_return_edge)
    with `CFG_node (targetnode a) \<in> sum_SDG_slice2 n'`
    have "CFG_node (sourcenode a) \<in> sum_SDG_slice2 n'"
      by(fastsimp intro:sum_SDG_slice2.intros)
    with `n' \<in> sum_SDG_slice1 n\<^isub>c` `n'' s-p'\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')`
    show ?case by(fastsimp intro:combine_SDG_slices.combSlice_Return_parent_node 
                            simp:HRB_slice_def)
  qed
  from `valid_edge a'` `kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'` `a \<in> get_return_edges a'`
  have "CFG_node (targetnode a') s\<longrightarrow>\<^bsub>cd\<^esub> CFG_node (sourcenode a)"
    by(fastsimp intro:sum_SDG_proc_entry_exit_cdep)
  with `CFG_node (sourcenode a) \<in> HRB_slice n\<^isub>c`
  show "CFG_node (targetnode a') \<in> HRB_slice n\<^isub>c"
    by(fastsimp elim!:combine_SDG_slices.cases 
                intro:combine_SDG_slices.intros cdep_slice1 cdep_slice2 
                 simp:HRB_slice_def)
qed



subsection {* Proof of precision *}


lemma in_intra_SDG_path_in_slice2:
  "\<lbrakk>n i-ns\<rightarrow>\<^isub>d* n'; n'' \<in> set ns\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice2 n'"
proof(induct rule:intra_SDG_path.induct)
  case iSp_Nil thus ?case by simp
next
  case (iSp_Append_cdep n ns nx n')
  note IH = `n'' \<in> set ns \<Longrightarrow> n'' \<in> sum_SDG_slice2 nx`
  from `n'' \<in> set (ns@[nx])` have "n'' \<in> set ns \<or> n'' = nx" by auto
  thus ?case
  proof
    assume "n'' \<in> set ns"
    from IH[OF this] have "n'' \<in> sum_SDG_slice2 nx" by simp
    with `nx \<longrightarrow>\<^bsub>cd\<^esub> n'` show ?thesis
      by(fastsimp intro:slice2_cdep_slice2 SDG_edge_sum_SDG_edge)
  next
    assume "n'' = nx"
    from `nx \<longrightarrow>\<^bsub>cd\<^esub> n'` have "valid_SDG_node n'" by(rule SDG_edge_valid_SDG_node)
    hence "n' \<in> sum_SDG_slice2 n'" by(rule refl_slice2)
    with `nx \<longrightarrow>\<^bsub>cd\<^esub> n'` have "nx \<in> sum_SDG_slice2 n'"
      by(fastsimp intro:cdep_slice2 SDG_edge_sum_SDG_edge)
    with `n'' = nx` show ?thesis by simp
  qed
next
  case (iSp_Append_ddep n ns nx V n')
  note IH = `n'' \<in> set ns \<Longrightarrow> n'' \<in> sum_SDG_slice2 nx`
  from `n'' \<in> set (ns@[nx])` have "n'' \<in> set ns \<or> n'' = nx" by auto
  thus ?case
  proof
    assume "n'' \<in> set ns"
    from IH[OF this] have "n'' \<in> sum_SDG_slice2 nx" by simp
    with `nx -V\<rightarrow>\<^bsub>dd\<^esub> n'` show ?thesis
      by(fastsimp intro:slice2_ddep_slice2 SDG_edge_sum_SDG_edge)
  next
    assume "n'' = nx"
    from `nx -V\<rightarrow>\<^bsub>dd\<^esub> n'` have "valid_SDG_node n'" by(rule SDG_edge_valid_SDG_node)
    hence "n' \<in> sum_SDG_slice2 n'" by(rule refl_slice2)
    with `nx -V\<rightarrow>\<^bsub>dd\<^esub> n'` have "nx \<in> sum_SDG_slice2 n'"
      by(fastsimp intro:ddep_slice2 SDG_edge_sum_SDG_edge)
    with `n'' = nx` show ?thesis by simp
  qed
qed


lemma in_intra_SDG_path_in_HRB_slice:
  "\<lbrakk>n i-ns\<rightarrow>\<^isub>d* n'; n'' \<in> set ns\<rbrakk> \<Longrightarrow> n'' \<in> HRB_slice n'"
proof(induct rule:intra_SDG_path.induct)
  case iSp_Nil thus ?case by simp
next
  case (iSp_Append_cdep n ns nx n')
  note IH = `n'' \<in> set ns \<Longrightarrow> n'' \<in> HRB_slice nx`
  from `n'' \<in> set (ns@[nx])` have "n'' \<in> set ns \<or> n'' = nx" by auto
  thus ?case
  proof
    assume "n'' \<in> set ns"
    from IH[OF `n'' \<in> set ns`] have "n'' \<in> HRB_slice nx" .
    from this `nx \<longrightarrow>\<^bsub>cd\<^esub> n'` show ?case
      apply(auto simp:HRB_slice_def)
      apply(induct rule:combine_SDG_slices.induct)
      by(fastsimp intro:combine_SDG_slices.intros 
                   elim:slice1_cdep_slice1 SDG_edge_sum_SDG_edge)+
  next
    assume "n'' = nx"
    from `nx \<longrightarrow>\<^bsub>cd\<^esub> n'` have "valid_SDG_node n'" by(rule SDG_edge_valid_SDG_node)
    hence "n' \<in> sum_SDG_slice1 n'" by(rule refl_slice1)
    with `nx \<longrightarrow>\<^bsub>cd\<^esub> n'` have "nx \<in> sum_SDG_slice1 n'" 
      by(fastsimp intro:cdep_slice1 SDG_edge_sum_SDG_edge)
    with `n'' = nx` show ?case by(fastsimp intro:combSlice_refl simp:HRB_slice_def)
  qed
next
  case (iSp_Append_ddep n ns nx V n')
  note IH = `n'' \<in> set ns \<Longrightarrow> n'' \<in> HRB_slice nx`
  from `n'' \<in> set (ns@[nx])` have "n'' \<in> set ns \<or> n'' = nx" by auto
  thus ?case
  proof
    assume "n'' \<in> set ns"
    from IH[OF `n'' \<in> set ns`] have "n'' \<in> HRB_slice nx" .
    from this `nx -V\<rightarrow>\<^bsub>dd\<^esub> n'` show ?case
      apply(auto simp:HRB_slice_def)
      apply(induct rule:combine_SDG_slices.induct)
      by(fastsimp intro:combine_SDG_slices.intros 
                   elim:slice1_ddep_slice1 SDG_edge_sum_SDG_edge)+
  next
    assume "n'' = nx"
    from `nx -V\<rightarrow>\<^bsub>dd\<^esub> n'` have "valid_SDG_node n'" by(rule SDG_edge_valid_SDG_node)
    hence "n' \<in> sum_SDG_slice1 n'" by(rule refl_slice1)
    with `nx -V\<rightarrow>\<^bsub>dd\<^esub> n'` have "nx \<in> sum_SDG_slice1 n'" 
      by(fastsimp intro:ddep_slice1 SDG_edge_sum_SDG_edge)
    with `n'' = nx` show ?case by(fastsimp intro:combSlice_refl simp:HRB_slice_def)
  qed
qed


lemma in_matched_in_slice2:
  "\<lbrakk>matched n ns n'; n'' \<in> set ns\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice2 n'"
proof(induct rule:matched.induct)
  case matched_Nil thus ?case by simp
next
  case (matched_Append_intra_SDG_path n ns nx ns' n')
  note IH = `n'' \<in> set ns \<Longrightarrow> n'' \<in> sum_SDG_slice2 nx`
  from `n'' \<in> set (ns@ns')` have "n'' \<in> set ns \<or> n'' \<in> set ns'" by simp
  thus ?case
  proof
    assume "n'' \<in> set ns"
    from IH[OF this] have "n'' \<in> sum_SDG_slice2 nx" .
    with `nx i-ns'\<rightarrow>\<^isub>d* n'` show ?thesis
      by(fastsimp intro:slice2_is_SDG_path_slice2 
	                intra_SDG_path_is_SDG_path)
  next
    assume "n'' \<in> set ns'"
    with `nx i-ns'\<rightarrow>\<^isub>d* n'` show ?case by(rule in_intra_SDG_path_in_slice2)
  qed
next
  case (matched_bracket_call n\<^isub>0 ns n\<^isub>1 p n\<^isub>2 ns' n\<^isub>3 n\<^isub>4 V a a')
  note IH1 = `n'' \<in> set ns \<Longrightarrow> n'' \<in> sum_SDG_slice2 n\<^isub>1`
  note IH2 = `n'' \<in> set ns' \<Longrightarrow> n'' \<in> sum_SDG_slice2 n\<^isub>3`
  from `n\<^isub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^isub>2` `matched n\<^isub>2 ns' n\<^isub>3` `n\<^isub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^isub>4 \<or> n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4` 
    `a' \<in> get_return_edges a` `valid_edge a`
    `sourcenode a = parent_node n\<^isub>1` `targetnode a = parent_node n\<^isub>2`
    `sourcenode a' = parent_node n\<^isub>3` `targetnode a' = parent_node n\<^isub>4`
  have "matched n\<^isub>1 ([]@n\<^isub>1#ns'@[n\<^isub>3]) n\<^isub>4"
    by(fastsimp intro:matched.matched_bracket_call matched_Nil 
                 elim:SDG_edge_valid_SDG_node)
  then obtain nsx where "n\<^isub>1 is-nsx\<rightarrow>\<^isub>d* n\<^isub>4" by(erule matched_is_SDG_path)
  from `n'' \<in> set (ns@n\<^isub>1#ns'@[n\<^isub>3])` 
  have "((n'' \<in> set ns \<or> n'' = n\<^isub>1) \<or> n'' \<in> set ns') \<or> n'' = n\<^isub>3" by auto
  thus ?case apply -
  proof(erule disjE)+
    assume "n'' \<in> set ns"
    from IH1[OF this] have "n'' \<in> sum_SDG_slice2 n\<^isub>1" .
    with `n\<^isub>1 is-nsx\<rightarrow>\<^isub>d* n\<^isub>4` show ?thesis 
      by -(rule slice2_is_SDG_path_slice2)
  next
    assume "n'' = n\<^isub>1"
    from `n\<^isub>1 is-nsx\<rightarrow>\<^isub>d* n\<^isub>4` have "n\<^isub>1 \<in> sum_SDG_slice2 n\<^isub>4" 
      by(fastsimp intro:is_SDG_path_slice2 refl_slice2 is_SDG_path_valid_SDG_node)
    with `n'' = n\<^isub>1` show ?thesis by(fastsimp intro:combSlice_refl simp:HRB_slice_def)
  next
    assume "n'' \<in> set ns'"
    from IH2[OF this] have "n'' \<in> sum_SDG_slice2 n\<^isub>3" .
    with `n\<^isub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^isub>4 \<or> n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4` show ?thesis 
      by(fastsimp intro:slice2_ret_slice2 slice2_param_out_slice2 
	                SDG_edge_sum_SDG_edge)
  next
    assume "n'' = n\<^isub>3"
    from `n\<^isub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^isub>4 \<or> n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4` have "n\<^isub>3 s-p\<rightarrow>\<^bsub>ret\<^esub> n\<^isub>4 \<or> n\<^isub>3 s-p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4" 
      by(fastsimp intro:SDG_edge_sum_SDG_edge)
    hence "n\<^isub>3 \<in> sum_SDG_slice2 n\<^isub>4"
      by(fastsimp intro:return_slice2 param_out_slice2 refl_slice2 
	                sum_SDG_edge_valid_SDG_node)
    with `n'' = n\<^isub>3` show ?thesis by simp
  qed
next
  case (matched_bracket_param n\<^isub>0 ns n\<^isub>1 p V n\<^isub>2 ns' n\<^isub>3 n\<^isub>4 a a')
  note IH1 = `n'' \<in> set ns \<Longrightarrow> n'' \<in> sum_SDG_slice2 n\<^isub>1`
  note IH2 = `n'' \<in> set ns' \<Longrightarrow> n'' \<in> sum_SDG_slice2 n\<^isub>3`
  from `n\<^isub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^isub>2` `matched n\<^isub>2 ns' n\<^isub>3` `n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4` 
    `a' \<in> get_return_edges a` `valid_edge a`
    `sourcenode a = parent_node n\<^isub>1` `targetnode a = parent_node n\<^isub>2`
    `sourcenode a' = parent_node n\<^isub>3` `targetnode a' = parent_node n\<^isub>4`
  have "matched n\<^isub>1 ([]@n\<^isub>1#ns'@[n\<^isub>3]) n\<^isub>4"
    by(fastsimp intro:matched.matched_bracket_param matched_Nil 
	         elim:SDG_edge_valid_SDG_node)
  then obtain nsx where "n\<^isub>1 is-nsx\<rightarrow>\<^isub>d* n\<^isub>4" by(erule matched_is_SDG_path)
  from `n'' \<in> set (ns@n\<^isub>1#ns'@[n\<^isub>3])` 
  have "((n'' \<in> set ns \<or> n'' = n\<^isub>1) \<or> n'' \<in> set ns') \<or> n'' = n\<^isub>3" by auto
  thus ?case apply -
  proof(erule disjE)+
    assume "n'' \<in> set ns"
    from IH1[OF this] have "n'' \<in> sum_SDG_slice2 n\<^isub>1" .
    with `n\<^isub>1 is-nsx\<rightarrow>\<^isub>d* n\<^isub>4` show ?thesis 
      by -(rule slice2_is_SDG_path_slice2)
  next
    assume "n'' = n\<^isub>1"
    from `n\<^isub>1 is-nsx\<rightarrow>\<^isub>d* n\<^isub>4` have "n\<^isub>1 \<in> sum_SDG_slice2 n\<^isub>4" 
      by(fastsimp intro:is_SDG_path_slice2 refl_slice2 is_SDG_path_valid_SDG_node)
    with `n'' = n\<^isub>1` show ?thesis by(fastsimp intro:combSlice_refl simp:HRB_slice_def)
  next
    assume "n'' \<in> set ns'"
    from IH2[OF this] have "n'' \<in> sum_SDG_slice2 n\<^isub>3" .
    with `n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4` show ?thesis 
      by(fastsimp intro:slice2_param_out_slice2 SDG_edge_sum_SDG_edge)
  next
    assume "n'' = n\<^isub>3"
    from `n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4` have "n\<^isub>3 s-p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4" by(rule SDG_edge_sum_SDG_edge)
    hence "n\<^isub>3 \<in> sum_SDG_slice2 n\<^isub>4"
      by(fastsimp intro:param_out_slice2 refl_slice2 sum_SDG_edge_valid_SDG_node)
    with `n'' = n\<^isub>3` show ?thesis by simp
  qed
qed


lemma in_matched_in_HRB_slice:
  "\<lbrakk>matched n ns n'; n'' \<in> set ns\<rbrakk> \<Longrightarrow> n'' \<in> HRB_slice n'"
proof(induct rule:matched.induct)
   case matched_Nil thus ?case by simp
next
  case (matched_Append_intra_SDG_path n ns nx ns' n')
  note IH = `n'' \<in> set ns \<Longrightarrow> n'' \<in> HRB_slice nx`
  from `n'' \<in> set (ns@ns')` have "n'' \<in> set ns \<or> n'' \<in> set ns'" by simp
  thus ?case
  proof
    assume "n'' \<in> set ns"
    from IH[OF this] have "n'' \<in> HRB_slice nx" .
    with `nx i-ns'\<rightarrow>\<^isub>d* n'` show ?thesis
      by(fastsimp intro:HRB_slice_is_SDG_path_HRB_slice 
	                intra_SDG_path_is_SDG_path)
  next
    assume "n'' \<in> set ns'"
    with `nx i-ns'\<rightarrow>\<^isub>d* n'` show ?case by(rule in_intra_SDG_path_in_HRB_slice)
  qed
next
  case (matched_bracket_call n\<^isub>0 ns n\<^isub>1 p n\<^isub>2 ns' n\<^isub>3 n\<^isub>4 V a a')
  note IH1 = `n'' \<in> set ns \<Longrightarrow> n'' \<in> HRB_slice n\<^isub>1`
  note IH2 = `n'' \<in> set ns' \<Longrightarrow> n'' \<in> HRB_slice n\<^isub>3`
  from `n\<^isub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^isub>2` `matched n\<^isub>2 ns' n\<^isub>3` `n\<^isub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^isub>4 \<or> n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4` 
    `a' \<in> get_return_edges a` `valid_edge a`
    `sourcenode a = parent_node n\<^isub>1` `targetnode a = parent_node n\<^isub>2`
    `sourcenode a' = parent_node n\<^isub>3` `targetnode a' = parent_node n\<^isub>4`
  have "matched n\<^isub>1 ([]@n\<^isub>1#ns'@[n\<^isub>3]) n\<^isub>4"
    by(fastsimp intro:matched.matched_bracket_call matched_Nil 
                 elim:SDG_edge_valid_SDG_node)
  then obtain nsx where "n\<^isub>1 is-nsx\<rightarrow>\<^isub>d* n\<^isub>4" by(erule matched_is_SDG_path)
  from `n'' \<in> set (ns@n\<^isub>1#ns'@[n\<^isub>3])` 
  have "((n'' \<in> set ns \<or> n'' = n\<^isub>1) \<or> n'' \<in> set ns') \<or> n'' = n\<^isub>3" by auto
  thus ?case apply -
  proof(erule disjE)+
    assume "n'' \<in> set ns"
    from IH1[OF this] have "n'' \<in> HRB_slice n\<^isub>1" .
    with `n\<^isub>1 is-nsx\<rightarrow>\<^isub>d* n\<^isub>4` show ?thesis 
      by -(rule HRB_slice_is_SDG_path_HRB_slice)
  next
    assume "n'' = n\<^isub>1"
    from `n\<^isub>1 is-nsx\<rightarrow>\<^isub>d* n\<^isub>4` have "n\<^isub>1 \<in> sum_SDG_slice1 n\<^isub>4" 
      by(fastsimp intro:is_SDG_path_slice1 refl_slice1 is_SDG_path_valid_SDG_node)
    with `n'' = n\<^isub>1` show ?thesis by(fastsimp intro:combSlice_refl simp:HRB_slice_def)
  next
    assume "n'' \<in> set ns'"
    with `matched n\<^isub>2 ns' n\<^isub>3` have "n'' \<in> sum_SDG_slice2 n\<^isub>3"
      by(rule in_matched_in_slice2)
    with `n\<^isub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^isub>4 \<or> n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4` have "n'' \<in> sum_SDG_slice2 n\<^isub>4"
      by(fastsimp intro:slice2_ret_slice2 slice2_param_out_slice2 
	                SDG_edge_sum_SDG_edge)
    from `n\<^isub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^isub>4 \<or> n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4` have "valid_SDG_node n\<^isub>4"
      by(fastsimp intro:SDG_edge_valid_SDG_node)
    hence "n\<^isub>4 \<in> sum_SDG_slice1 n\<^isub>4" by(rule refl_slice1)
    from `n\<^isub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^isub>4 \<or> n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4`
    have "CFG_node (parent_node n\<^isub>3) -p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n\<^isub>4)"
      by(fastsimp elim:SDG_edge.cases intro:SDG_return_edge)
    with `n'' \<in> sum_SDG_slice2 n\<^isub>4` `n\<^isub>4 \<in> sum_SDG_slice1 n\<^isub>4`
    have "n'' \<in> combine_SDG_slices (sum_SDG_slice1 n\<^isub>4)"
      by(fastsimp intro:combSlice_Return_parent_node SDG_edge_sum_SDG_edge)
    thus ?case by(simp add:HRB_slice_def)
  next
    assume "n'' = n\<^isub>3"
    from `n\<^isub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^isub>4 \<or> n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4`
    have "CFG_node (parent_node n\<^isub>3) -p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n\<^isub>4)"
      by(fastsimp elim:SDG_edge.cases intro:SDG_return_edge)
    from `n\<^isub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^isub>4 \<or> n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4` have "valid_SDG_node n\<^isub>4"
      by(fastsimp intro:SDG_edge_valid_SDG_node)
    hence "n\<^isub>4 \<in> sum_SDG_slice1 n\<^isub>4" by(rule refl_slice1)
    from `valid_SDG_node n\<^isub>4` have "n\<^isub>4 \<in> sum_SDG_slice2 n\<^isub>4" by(rule refl_slice2)
    with `n\<^isub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^isub>4 \<or> n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4` have "n\<^isub>3 \<in> sum_SDG_slice2 n\<^isub>4" 
      by(fastsimp intro:return_slice2 param_out_slice2 SDG_edge_sum_SDG_edge)
    with `n\<^isub>4 \<in> sum_SDG_slice1 n\<^isub>4` 
      `CFG_node (parent_node n\<^isub>3) -p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n\<^isub>4)` `n'' = n\<^isub>3`
    have "n'' \<in> combine_SDG_slices (sum_SDG_slice1 n\<^isub>4)"
      by(fastsimp intro:combSlice_Return_parent_node SDG_edge_sum_SDG_edge)
    thus ?case by(simp add:HRB_slice_def)
  qed
next
  case (matched_bracket_param n\<^isub>0 ns n\<^isub>1 p V n\<^isub>2 ns' n\<^isub>3 n\<^isub>4 a a')
  note IH1 = `n'' \<in> set ns \<Longrightarrow> n'' \<in> HRB_slice n\<^isub>1`
  note IH2 = `n'' \<in> set ns' \<Longrightarrow> n'' \<in> HRB_slice n\<^isub>3`
  from `n\<^isub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^isub>2` `matched n\<^isub>2 ns' n\<^isub>3` `n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4` 
    `a' \<in> get_return_edges a` `valid_edge a`
    `sourcenode a = parent_node n\<^isub>1` `targetnode a = parent_node n\<^isub>2`
    `sourcenode a' = parent_node n\<^isub>3` `targetnode a' = parent_node n\<^isub>4`
  have "matched n\<^isub>1 ([]@n\<^isub>1#ns'@[n\<^isub>3]) n\<^isub>4"
    by(fastsimp intro:matched.matched_bracket_param matched_Nil 
	         elim:SDG_edge_valid_SDG_node)
  then obtain nsx where "n\<^isub>1 is-nsx\<rightarrow>\<^isub>d* n\<^isub>4" by(erule matched_is_SDG_path)
  from `n'' \<in> set (ns@n\<^isub>1#ns'@[n\<^isub>3])` 
  have "((n'' \<in> set ns \<or> n'' = n\<^isub>1) \<or> n'' \<in> set ns') \<or> n'' = n\<^isub>3" by auto
  thus ?case apply -
  proof(erule disjE)+
    assume "n'' \<in> set ns"
    from IH1[OF this] have "n'' \<in> HRB_slice n\<^isub>1" .
    with `n\<^isub>1 is-nsx\<rightarrow>\<^isub>d* n\<^isub>4` show ?thesis 
      by -(rule HRB_slice_is_SDG_path_HRB_slice)
  next
    assume "n'' = n\<^isub>1"
    from `n\<^isub>1 is-nsx\<rightarrow>\<^isub>d* n\<^isub>4` have "n\<^isub>1 \<in> sum_SDG_slice1 n\<^isub>4"
      by(fastsimp intro:is_SDG_path_slice1 refl_slice1 is_SDG_path_valid_SDG_node)
    with `n'' = n\<^isub>1` show ?thesis by(fastsimp intro:combSlice_refl simp:HRB_slice_def)
  next
    assume "n'' \<in> set ns'"
    with `matched n\<^isub>2 ns' n\<^isub>3` have "n'' \<in> sum_SDG_slice2 n\<^isub>3"
      by(rule in_matched_in_slice2)
    with `n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4` have "n'' \<in> sum_SDG_slice2 n\<^isub>4"
      by(fastsimp intro:slice2_param_out_slice2 SDG_edge_sum_SDG_edge)
    from `n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4` have "valid_SDG_node n\<^isub>4" by(rule SDG_edge_valid_SDG_node)
    hence "n\<^isub>4 \<in> sum_SDG_slice1 n\<^isub>4" by(rule refl_slice1)
    from `n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4` 
    have "CFG_node (parent_node n\<^isub>3) -p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n\<^isub>4)"
      by(fastsimp elim:SDG_edge.cases intro:SDG_return_edge)
    with `n'' \<in> sum_SDG_slice2 n\<^isub>4` `n\<^isub>4 \<in> sum_SDG_slice1 n\<^isub>4`
    have "n'' \<in> combine_SDG_slices (sum_SDG_slice1 n\<^isub>4)"
      by(fastsimp intro:combSlice_Return_parent_node SDG_edge_sum_SDG_edge)
    thus ?case by(simp add:HRB_slice_def)
  next
    assume "n'' = n\<^isub>3"
    from `n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4` have "n\<^isub>3 s-p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4" by(rule SDG_edge_sum_SDG_edge)
    from `n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4` have "valid_SDG_node n\<^isub>4" by(rule SDG_edge_valid_SDG_node)
    hence "n\<^isub>4 \<in> sum_SDG_slice1 n\<^isub>4" by(rule refl_slice1)
    from `valid_SDG_node n\<^isub>4` have "n\<^isub>4 \<in> sum_SDG_slice2 n\<^isub>4" by(rule refl_slice2)
    with `n\<^isub>3 s-p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4` have "n\<^isub>3 \<in> sum_SDG_slice2 n\<^isub>4" by(rule param_out_slice2)
    from `n\<^isub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^isub>4` 
    have "CFG_node (parent_node n\<^isub>3) -p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n\<^isub>4)"
      by(fastsimp elim:SDG_edge.cases intro:SDG_return_edge)
    with `n\<^isub>3 \<in> sum_SDG_slice2 n\<^isub>4` `n\<^isub>4 \<in> sum_SDG_slice1 n\<^isub>4` `n'' = n\<^isub>3` show ?thesis
      by(fastsimp intro:combSlice_Return_parent_node SDG_edge_sum_SDG_edge 
	           simp:HRB_slice_def)
  qed
qed


theorem in_realizable_in_HRB_slice:
  "\<lbrakk>realizable n ns n'; n'' \<in> set ns\<rbrakk> \<Longrightarrow> n'' \<in> HRB_slice n'"
proof(induct rule:realizable.induct)
  case (realizable_matched n ns n')
  from `matched n ns n'` `n'' \<in> set ns` show ?case by(rule in_matched_in_HRB_slice)
next
  case (realizable_call n\<^isub>0 ns n\<^isub>1 p n\<^isub>2 V ns' n\<^isub>3)
  note IH = `n'' \<in> set ns \<Longrightarrow> n'' \<in> HRB_slice n\<^isub>1`
  from `n'' \<in> set (ns@n\<^isub>1#ns')` have "(n'' \<in> set ns \<or> n'' = n\<^isub>1) \<or> n'' \<in> set ns'"
    by auto
  thus ?case apply -
  proof(erule disjE)+
    assume "n'' \<in> set ns"
    from IH[OF this] have "n'' \<in> combine_SDG_slices (sum_SDG_slice1 n\<^isub>1)"
      by(simp add:HRB_slice_def)
    hence "n'' \<in> HRB_slice n\<^isub>2"
    proof(induct rule:combine_SDG_slices.induct)
      case (combSlice_refl n)
      from `n \<in> sum_SDG_slice1 n\<^isub>1` `n\<^isub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^isub>2 \<or> n\<^isub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^isub>2`
      have "n \<in> sum_SDG_slice1 n\<^isub>2" 
	by(fastsimp intro:slice1_call_slice1 slice1_param_in_slice1 
	                  SDG_edge_sum_SDG_edge)
      thus ?case 
	by(fastsimp intro:combine_SDG_slices.combSlice_refl simp:HRB_slice_def)
    next
      case (combSlice_Return_parent_node n' n'' p' n)
      from `n' \<in> sum_SDG_slice1 n\<^isub>1` `n\<^isub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^isub>2 \<or> n\<^isub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^isub>2`
      have "n' \<in> sum_SDG_slice1 n\<^isub>2" 
	by(fastsimp intro:slice1_call_slice1 slice1_param_in_slice1 
	                  SDG_edge_sum_SDG_edge)
      with `n'' s-p'\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')` `n \<in> sum_SDG_slice2 n'` show ?case
	by(fastsimp intro:combine_SDG_slices.combSlice_Return_parent_node 
	             simp:HRB_slice_def)
    qed
    from `matched n\<^isub>2 ns' n\<^isub>3` obtain nsx where "n\<^isub>2 is-nsx\<rightarrow>\<^isub>d* n\<^isub>3"
      by(erule matched_is_SDG_path)
    with `n'' \<in> HRB_slice n\<^isub>2` show ?thesis
      by(fastsimp intro:HRB_slice_is_SDG_path_HRB_slice)
  next
    assume "n'' = n\<^isub>1"
    from `matched n\<^isub>2 ns' n\<^isub>3` obtain nsx where "n\<^isub>2 is-nsx\<rightarrow>\<^isub>d* n\<^isub>3"
      by(erule matched_is_SDG_path)
    hence "n\<^isub>2 \<in> sum_SDG_slice1 n\<^isub>2" 
      by(fastsimp intro:refl_slice1 is_SDG_path_valid_SDG_node)
    with `n\<^isub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^isub>2 \<or> n\<^isub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^isub>2`
    have "n\<^isub>1 \<in> sum_SDG_slice1 n\<^isub>2"
      by(fastsimp intro:call_slice1 param_in_slice1 SDG_edge_sum_SDG_edge)
    hence "n\<^isub>1 \<in> HRB_slice n\<^isub>2" by(fastsimp intro:combSlice_refl simp:HRB_slice_def)
    with `n\<^isub>2 is-nsx\<rightarrow>\<^isub>d* n\<^isub>3` `n'' = n\<^isub>1` show ?thesis
      by(fastsimp intro:HRB_slice_is_SDG_path_HRB_slice)
  next
    assume "n'' \<in> set ns'"
    with `matched n\<^isub>2 ns' n\<^isub>3` show ?thesis by(rule in_matched_in_HRB_slice)
  qed
qed


lemma slice1_ics_SDG_path:
  assumes "n \<in> sum_SDG_slice1 n'"
  obtains "n = n'"
  | ns where "CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n'" and "n \<in> set ns"
proof(atomize_elim)
  from `n \<in> sum_SDG_slice1 n'`
  show "n = n' \<or> (\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns)"
  proof(induct rule:sum_SDG_slice1.induct)
    case refl_slice1 thus ?case by simp
  next
    case (cdep_slice1 n'' n)
    from `n'' s\<longrightarrow>\<^bsub>cd\<^esub> n` have "valid_SDG_node n''" by(rule sum_SDG_edge_valid_SDG_node)
    hence "n'' ics-[]\<rightarrow>\<^isub>d* n''" by(rule icsSp_Nil)
    from `valid_SDG_node n''` have "valid_node (parent_node n'')"
      by(rule valid_SDG_CFG_node)
    thus ?case
    proof(cases "parent_node n''" rule:valid_node_cases)
      case Entry
      with `valid_SDG_node n''` have "n'' = CFG_node (_Entry_)"
	by(rule valid_SDG_node_parent_Entry)
      from `n'' ics-[]\<rightarrow>\<^isub>d* n''` `n'' s\<longrightarrow>\<^bsub>cd\<^esub> n`  have "n'' ics-[]@[n'']\<rightarrow>\<^isub>d* n"
	by -(rule icsSp_Append_cdep)
      from `n = n' \<or> (\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns)`
      show ?thesis
      proof
	assume "n = n'"
	with `n'' = CFG_node (_Entry_)` `n'' ics-[]@[n'']\<rightarrow>\<^isub>d* n` 
	show ?thesis by fastsimp
      next
	assume "\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns"
	then obtain ns where "CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n'" and "n \<in> set ns"
	  by blast
	then obtain ns' ns'' where "ns = ns'@ns''" and "n ics-ns''\<rightarrow>\<^isub>d* n'"
	  by -(erule ics_SDG_path_split)
	with `n'' = CFG_node (_Entry_)` `n'' ics-[]@[n'']\<rightarrow>\<^isub>d* n`
	show ?thesis by(fastsimp intro:ics_SDG_path_Append)
      qed
    next
      case Exit
      with `valid_SDG_node n''` have "n'' = CFG_node (_Exit_)"
	by(rule valid_SDG_node_parent_Exit)
      with `n'' s\<longrightarrow>\<^bsub>cd\<^esub> n` have False by(fastsimp intro:Exit_no_sum_SDG_edge_source)
      thus ?thesis by simp
    next
      case inner
      from `n'' s\<longrightarrow>\<^bsub>cd\<^esub> n` have "valid_SDG_node n''"
	by(rule sum_SDG_edge_valid_SDG_node)
      with `inner_node (parent_node n'')` obtain ns 
	where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^isub>d* n''"
	by(erule Entry_cc_SDG_path_to_inner_node)
      with `n'' s\<longrightarrow>\<^bsub>cd\<^esub> n` have "CFG_node (_Entry_) cc-ns@[n'']\<rightarrow>\<^isub>d* n"
	by(fastsimp intro:ccSp_Append_cdep sum_SDG_edge_SDG_edge)
      hence "CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^isub>d* n"
	by(rule cc_SDG_path_ics_SDG_path)
      from `n = n' \<or> (\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns)`
      show ?thesis
      proof
	assume "n = n'"
	with `CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^isub>d* n` show ?thesis by fastsimp
      next
	assume "\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns"
	then obtain nsx where "CFG_node (_Entry_) ics-nsx\<rightarrow>\<^isub>d* n'" and "n \<in> set nsx"
	  by blast
	then obtain ns' ns'' where "nsx = ns'@ns''" and "n ics-ns''\<rightarrow>\<^isub>d* n'"
	  by -(erule ics_SDG_path_split)
	with `CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^isub>d* n`
	show ?thesis by(fastsimp intro:ics_SDG_path_Append)
      qed
    qed
  next
    case (ddep_slice1 n'' V n)
    from `n'' s-V\<rightarrow>\<^bsub>dd\<^esub> n` have "valid_SDG_node n''" by(rule sum_SDG_edge_valid_SDG_node)
    hence "n'' ics-[]\<rightarrow>\<^isub>d* n''" by(rule icsSp_Nil)
    from `valid_SDG_node n''` have "valid_node (parent_node n'')"
      by(rule valid_SDG_CFG_node)
    thus ?case
    proof(cases "parent_node n''" rule:valid_node_cases)
      case Entry
      with `valid_SDG_node n''` have "n'' = CFG_node (_Entry_)"
	by(rule valid_SDG_node_parent_Entry)
      from `n'' s-V\<rightarrow>\<^bsub>dd\<^esub> n` have "V \<in> Def\<^bsub>SDG\<^esub> n''"
	by(fastsimp elim:sum_SDG_edge.cases simp:data_dependence_def)
      with `n'' = CFG_node (_Entry_)` Entry_empty
      have False by(fastsimp elim:SDG_Def.cases)
      thus ?thesis by simp
    next
      case Exit
      with `valid_SDG_node n''` have "n'' = CFG_node (_Exit_)"
	by(rule valid_SDG_node_parent_Exit)
      with `n'' s-V\<rightarrow>\<^bsub>dd\<^esub> n` have False by(fastsimp intro:Exit_no_sum_SDG_edge_source)
      thus ?thesis by simp
    next
      case inner
      from `n'' s-V\<rightarrow>\<^bsub>dd\<^esub> n` have "valid_SDG_node n''"
	by(rule sum_SDG_edge_valid_SDG_node)
      with `inner_node (parent_node n'')` obtain ns 
	where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^isub>d* n''"
	by(erule Entry_cc_SDG_path_to_inner_node)
      hence "CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n''"
	by(rule cc_SDG_path_ics_SDG_path)
      show ?thesis
      proof(cases "n'' = n")
	case True
	from `n = n' \<or> (\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns)`
	show ?thesis
	proof
	  assume "n = n'"
	  with `n'' = n` show ?thesis by simp
	next
	  assume "\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns"
	  with `n'' = n` show ?thesis by fastsimp
	qed
      next
	case False
	with `n'' s-V\<rightarrow>\<^bsub>dd\<^esub> n` `CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n''`
	have "CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^isub>d* n"
	  by -(rule icsSp_Append_ddep)
	from `n = n' \<or> (\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns)`
	show ?thesis
	proof
	  assume "n = n'"
	  with `CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^isub>d* n` show ?thesis by fastsimp
	next
	  assume "\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns"
	  then obtain nsx where "CFG_node (_Entry_) ics-nsx\<rightarrow>\<^isub>d* n'" and "n \<in> set nsx"
	    by blast
	  then obtain ns' ns'' where "nsx = ns'@ns''" and "n ics-ns''\<rightarrow>\<^isub>d* n'"
	    by -(erule ics_SDG_path_split)
	  with `CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^isub>d* n`
	  show ?thesis by(fastsimp intro:ics_SDG_path_Append)
	qed
      qed
    qed
  next
    case (call_slice1 n'' p n)
    from `n'' s-p\<rightarrow>\<^bsub>call\<^esub> n` have "valid_SDG_node n''" 
      by(rule sum_SDG_edge_valid_SDG_node)
    hence "n'' ics-[]\<rightarrow>\<^isub>d* n''" by(rule icsSp_Nil)
    from `valid_SDG_node n''` have "valid_node (parent_node n'')"
      by(rule valid_SDG_CFG_node)
    thus ?case
    proof(cases "parent_node n''" rule:valid_node_cases)
      case Entry
      with `valid_SDG_node n''` have "n'' = CFG_node (_Entry_)"
	by(rule valid_SDG_node_parent_Entry)
      from `n'' ics-[]\<rightarrow>\<^isub>d* n''` `n'' s-p\<rightarrow>\<^bsub>call\<^esub> n`  have "n'' ics-[]@[n'']\<rightarrow>\<^isub>d* n"
	by -(rule icsSp_Append_call)
      from `n = n' \<or> (\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns)`
      show ?thesis
      proof
	assume "n = n'"
	with `n'' = CFG_node (_Entry_)` `n'' ics-[]@[n'']\<rightarrow>\<^isub>d* n` 
	show ?thesis by fastsimp
      next
	assume "\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns"
	then obtain ns where "CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n'" and "n \<in> set ns"
	  by blast
	then obtain ns' ns'' where "ns = ns'@ns''" and "n ics-ns''\<rightarrow>\<^isub>d* n'"
	  by -(erule ics_SDG_path_split)
	with `n'' = CFG_node (_Entry_)` `n'' ics-[]@[n'']\<rightarrow>\<^isub>d* n`
	show ?thesis by(fastsimp intro:ics_SDG_path_Append)
      qed
    next
      case Exit
      with `valid_SDG_node n''` have "n'' = CFG_node (_Exit_)"
	by(rule valid_SDG_node_parent_Exit)
      with `n'' s-p\<rightarrow>\<^bsub>call\<^esub> n` have False by(fastsimp intro:Exit_no_sum_SDG_edge_source)
      thus ?thesis by simp
    next
      case inner
      from `n'' s-p\<rightarrow>\<^bsub>call\<^esub> n` have "valid_SDG_node n''"
	by(rule sum_SDG_edge_valid_SDG_node)
      with `inner_node (parent_node n'')` obtain ns 
	where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^isub>d* n''"
	by(erule Entry_cc_SDG_path_to_inner_node)
      with `n'' s-p\<rightarrow>\<^bsub>call\<^esub> n` have "CFG_node (_Entry_) cc-ns@[n'']\<rightarrow>\<^isub>d* n"
	by(fastsimp intro:ccSp_Append_call sum_SDG_edge_SDG_edge)
      hence "CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^isub>d* n"
	by(rule cc_SDG_path_ics_SDG_path)
      from `n = n' \<or> (\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns)`
      show ?thesis
      proof
	assume "n = n'"
	with `CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^isub>d* n` show ?thesis by fastsimp
      next
	assume "\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns"
	then obtain nsx where "CFG_node (_Entry_) ics-nsx\<rightarrow>\<^isub>d* n'" and "n \<in> set nsx"
	  by blast
	then obtain ns' ns'' where "nsx = ns'@ns''" and "n ics-ns''\<rightarrow>\<^isub>d* n'"
	  by -(erule ics_SDG_path_split)
	with `CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^isub>d* n`
	show ?thesis by(fastsimp intro:ics_SDG_path_Append)
      qed
    qed
  next
    case (param_in_slice1 n'' p V n)
    from `n'' s-p:V\<rightarrow>\<^bsub>in\<^esub> n` have "valid_SDG_node n''" 
      by(rule sum_SDG_edge_valid_SDG_node)
    hence "n'' ics-[]\<rightarrow>\<^isub>d* n''" by(rule icsSp_Nil)
    from `valid_SDG_node n''` have "valid_node (parent_node n'')"
      by(rule valid_SDG_CFG_node)
    thus ?case
    proof(cases "parent_node n''" rule:valid_node_cases)
      case Entry
      with `valid_SDG_node n''` have "n'' = CFG_node (_Entry_)"
	by(rule valid_SDG_node_parent_Entry)
      from `n'' ics-[]\<rightarrow>\<^isub>d* n''` `n'' s-p:V\<rightarrow>\<^bsub>in\<^esub> n`  have "n'' ics-[]@[n'']\<rightarrow>\<^isub>d* n"
	by -(rule icsSp_Append_param_in)
      from `n = n' \<or> (\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns)`
      show ?thesis
      proof
	assume "n = n'"
	with `n'' = CFG_node (_Entry_)` `n'' ics-[]@[n'']\<rightarrow>\<^isub>d* n` 
	show ?thesis by fastsimp
      next
	assume "\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns"
	then obtain ns where "CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n'" and "n \<in> set ns"
	  by blast
	then obtain ns' ns'' where "ns = ns'@ns''" and "n ics-ns''\<rightarrow>\<^isub>d* n'"
	  by -(erule ics_SDG_path_split)
	with `n'' = CFG_node (_Entry_)` `n'' ics-[]@[n'']\<rightarrow>\<^isub>d* n`
	show ?thesis by(fastsimp intro:ics_SDG_path_Append)
      qed
    next
      case Exit
      with `valid_SDG_node n''` have "n'' = CFG_node (_Exit_)"
	by(rule valid_SDG_node_parent_Exit)
      with `n'' s-p:V\<rightarrow>\<^bsub>in\<^esub> n` have False by(fastsimp intro:Exit_no_sum_SDG_edge_source)
      thus ?thesis by simp
    next
      case inner
      from `n'' s-p:V\<rightarrow>\<^bsub>in\<^esub> n` have "valid_SDG_node n''"
	by(rule sum_SDG_edge_valid_SDG_node)
      with `inner_node (parent_node n'')` obtain ns 
	where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^isub>d* n''"
	by(erule Entry_cc_SDG_path_to_inner_node)
      hence "CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n''"
	by(rule cc_SDG_path_ics_SDG_path)
      with `n'' s-p:V\<rightarrow>\<^bsub>in\<^esub> n` have "CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^isub>d* n"
	by -(rule icsSp_Append_param_in)
      from `n = n' \<or> (\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns)`
      show ?thesis
      proof
	assume "n = n'"
	with `CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^isub>d* n` show ?thesis by fastsimp
      next
	assume "\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns"
	then obtain nsx where "CFG_node (_Entry_) ics-nsx\<rightarrow>\<^isub>d* n'" and "n \<in> set nsx"
	  by blast
	then obtain ns' ns'' where "nsx = ns'@ns''" and "n ics-ns''\<rightarrow>\<^isub>d* n'"
	  by -(erule ics_SDG_path_split)
	with `CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^isub>d* n`
	show ?thesis by(fastsimp intro:ics_SDG_path_Append)
      qed
    qed
  next
    case (sum_slice1 n'' p n)
    from `n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n` have "valid_SDG_node n''" 
      by(rule sum_SDG_edge_valid_SDG_node)
    hence "n'' ics-[]\<rightarrow>\<^isub>d* n''" by(rule icsSp_Nil)
    from `valid_SDG_node n''` have "valid_node (parent_node n'')"
      by(rule valid_SDG_CFG_node)
    thus ?case
    proof(cases "parent_node n''" rule:valid_node_cases)
      case Entry
      with `valid_SDG_node n''` have "n'' = CFG_node (_Entry_)"
	by(rule valid_SDG_node_parent_Entry)
      from `n'' ics-[]\<rightarrow>\<^isub>d* n''` `n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n`  have "n'' ics-[]@[n'']\<rightarrow>\<^isub>d* n"
	by -(rule icsSp_Append_sum)
      from `n = n' \<or> (\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns)`
      show ?thesis
      proof
	assume "n = n'"
	with `n'' = CFG_node (_Entry_)` `n'' ics-[]@[n'']\<rightarrow>\<^isub>d* n` 
	show ?thesis by fastsimp
      next
	assume "\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns"
	then obtain ns where "CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n'" and "n \<in> set ns"
	  by blast
	then obtain ns' ns'' where "ns = ns'@ns''" and "n ics-ns''\<rightarrow>\<^isub>d* n'"
	  by -(erule ics_SDG_path_split)
	with `n'' = CFG_node (_Entry_)` `n'' ics-[]@[n'']\<rightarrow>\<^isub>d* n`
	show ?thesis by(fastsimp intro:ics_SDG_path_Append)
      qed
    next
      case Exit
      with `valid_SDG_node n''` have "n'' = CFG_node (_Exit_)"
	by(rule valid_SDG_node_parent_Exit)
      with `n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n` have False by(fastsimp intro:Exit_no_sum_SDG_edge_source)
      thus ?thesis by simp
    next
      case inner
      from `n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n` have "valid_SDG_node n''"
	by(rule sum_SDG_edge_valid_SDG_node)
      with `inner_node (parent_node n'')` obtain ns 
	where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^isub>d* n''"
	by(erule Entry_cc_SDG_path_to_inner_node)
      hence "CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n''"
	by(rule cc_SDG_path_ics_SDG_path)
      with `n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n` have "CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^isub>d* n"
	by -(rule icsSp_Append_sum)
      from `n = n' \<or> (\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns)`
      show ?thesis
      proof
	assume "n = n'"
	with `CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^isub>d* n` show ?thesis by fastsimp
      next
	assume "\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^isub>d* n' \<and> n \<in> set ns"
	then obtain nsx where "CFG_node (_Entry_) ics-nsx\<rightarrow>\<^isub>d* n'" and "n \<in> set nsx"
	  by blast
	then obtain ns' ns'' where "nsx = ns'@ns''" and "n ics-ns''\<rightarrow>\<^isub>d* n'"
	  by -(erule ics_SDG_path_split)
	with `CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^isub>d* n`
	show ?thesis by(fastsimp intro:ics_SDG_path_Append)
      qed
    qed
  qed
qed


lemma slice2_irs_SDG_path:
  assumes "n \<in> sum_SDG_slice2 n'" and "valid_SDG_node n'"
  obtains ns where "n irs-ns\<rightarrow>\<^isub>d* n'"
using assms
by(induct rule:sum_SDG_slice2.induct,auto intro:intra_return_sum_SDG_path.intros)



lemma combine_SDG_slices_realizable:
  assumes "n \<in> combine_SDG_slices (sum_SDG_slice1 n')" and "valid_SDG_node n'"
  obtains "n = n'"
  | ns where "realizable (CFG_node (_Entry_)) ns n'" and "n \<in> set ns"
proof(atomize_elim)
  from `n \<in> combine_SDG_slices (sum_SDG_slice1 n')`
  show "n = n' \<or> (\<exists>ns. realizable (CFG_node (_Entry_)) ns n' \<and> n \<in> set ns)"
  proof(induct rule:combine_SDG_slices.induct)
    case (combSlice_refl n)
    from `n \<in> sum_SDG_slice1 n'` show ?case
      by(auto dest:slice1_ics_SDG_path ics_SDG_path_realizable)
  next
    case (combSlice_Return_parent_node nx n'' p n)
    from `nx \<in> sum_SDG_slice1 n'`
    show ?case
    proof(rule slice1_ics_SDG_path)
      assume "nx = n'"
      with `valid_SDG_node n'` `n \<in> sum_SDG_slice2 nx`
      obtain nsx where "n irs-nsx\<rightarrow>\<^isub>d* nx"
	by(fastsimp elim:slice2_irs_SDG_path)
      with `nx = n'` show ?thesis by(fastsimp elim:irs_SDG_path_realizable)
    next
      fix nsx' assume "CFG_node (_Entry_) ics-nsx'\<rightarrow>\<^isub>d* n'" and "nx \<in> set nsx'"
      from `nx \<in> sum_SDG_slice1 n'` `valid_SDG_node n'`
      have "valid_SDG_node nx"
	by(auto elim:slice1_ics_SDG_path ics_SDG_path_split 
	       intro:ics_SDG_path_valid_SDG_node)
      with `n \<in> sum_SDG_slice2 nx` obtain nsx where "n irs-nsx\<rightarrow>\<^isub>d* nx"
	by(fastsimp elim:slice2_irs_SDG_path)
      thus ?thesis
      proof(rule irs_SDG_path_realizable)
	assume "n = nx"
	with `CFG_node (_Entry_) ics-nsx'\<rightarrow>\<^isub>d* n'` `nx \<in> set nsx'`
	show ?thesis by(fastsimp elim:ics_SDG_path_realizable)
      next
	fix ns assume "realizable (CFG_node (_Entry_)) ns nx" and "n \<in> set ns"
	from `CFG_node (_Entry_) ics-nsx'\<rightarrow>\<^isub>d* n'` `nx \<in> set nsx'`
	obtain nsx' where "nx ics-nsx'\<rightarrow>\<^isub>d* n'" by -(erule ics_SDG_path_split)
	with `realizable (CFG_node (_Entry_)) ns nx`
	obtain ns' where "realizable (CFG_node (_Entry_)) (ns@ns') n'"
	  by(erule realizable_Append_ics_SDG_path)
	with `n \<in> set ns` show ?thesis by fastsimp
      qed
    qed
  qed
qed



theorem HRB_slice_realizable:
  assumes "n \<in> HRB_slice n'" and "valid_SDG_node n'"
  obtains "n = n'"
  | ns where "realizable (CFG_node (_Entry_)) ns n'" and "n \<in> set ns"
using assms
by(auto intro:combine_SDG_slices_realizable simp:HRB_slice_def)


theorem HRB_slice_precise:
  "\<lbrakk>valid_SDG_node n'; n \<noteq> n'\<rbrakk> \<Longrightarrow>
    n \<in> HRB_slice n' = (\<exists>ns. realizable (CFG_node (_Entry_)) ns n' \<and> n \<in> set ns)"
  by(fastsimp elim:HRB_slice_realizable intro:in_realizable_in_HRB_slice)


end

end