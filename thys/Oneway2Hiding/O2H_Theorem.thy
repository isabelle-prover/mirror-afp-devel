theory O2H_Theorem

imports Mixed_O2H

begin

unbundle cblinfun_syntax
unbundle lattice_syntax
unbundle register_syntax

section \<open>General O2H Setting and Theorem\<close>

text \<open>General O2H setting\<close>

locale o2h_theorem = o2h_setting "TYPE('x)" "TYPE('y::group_add)" "TYPE('mem)" "TYPE('l)" +
  fixes carrier :: "(('x \<Rightarrow> 'y)\<times>('x \<Rightarrow> 'y)\<times>('x \<Rightarrow> bool)\<times>_) set" 
  fixes distr :: "(('x \<Rightarrow> 'y)\<times>('x \<Rightarrow> 'y)\<times>('x \<Rightarrow> bool)\<times>_) \<Rightarrow> real"

assumes distr_pos: "\<forall>(H,G,S,z)\<in>carrier. distr (H,G,S,z) \<ge> 0"
  and distr_sum_1: "(\<Sum>(H,G,S,z)\<in>carrier. distr (H,G,S,z)) = 1"
  and finite_carrier: "finite carrier" 

and H_G_same_upto_S: 
"\<And>H G S z. (H,G,S,z)\<in>carrier \<Longrightarrow> x \<in> - Collect S \<Longrightarrow> H x = G x"

fixes E:: "'mem kraus_adv"
assumes E_norm_id: "\<And>i. i < d+1 \<Longrightarrow> kf_bound (E i) \<le> id_cblinfun"
assumes E_nonzero: "\<And>i. i < d+1 \<Longrightarrow> Rep_kraus_family (E i) \<noteq> {}"

fixes P:: "'mem update"
assumes is_Proj_P: "is_Proj P"

begin

lemma Fst_E_nonzero:
  "\<And>i. i < d+1 \<Longrightarrow> Rep_kraus_family (kf_Fst (E i)) \<noteq> {}"
  using E_nonzero by (simp add: kf_Fst.rep_eq)

text \<open>Some properties of the joint distribution.\<close>

lemma Uquery_G_H_same_on_not_S_embed':
  assumes "(H,G,S,z)\<in>carrier"
  shows
    "Uquery H o\<^sub>C\<^sub>L proj_classical_set (- (Collect S)) \<otimes>\<^sub>o id_cblinfun = 
 Uquery G o\<^sub>C\<^sub>L proj_classical_set (- (Collect S)) \<otimes>\<^sub>o id_cblinfun"
proof (intro equal_ket, safe, unfold tensor_ell2_ket[symmetric], goal_cases)
  case (1 a b)
  let ?P = "proj_classical_set (- (Collect S))"
  have "(Uquery H o\<^sub>C\<^sub>L ?P \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket a \<otimes>\<^sub>s ket b = 
    (Uquery G o\<^sub>C\<^sub>L ?P \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket a \<otimes>\<^sub>s ket b"
    if "\<not> S a"
  proof -
    have "(Uquery H o\<^sub>C\<^sub>L ?P \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket a \<otimes>\<^sub>s ket b = Uquery H *\<^sub>V ket a \<otimes>\<^sub>s ket b"
      by (simp add: proj_classical_set_elem tensor_op_ell2 that)
    also have "\<dots> = ket a \<otimes>\<^sub>s ket (b + H a)" using Uquery_ket by auto
    also have "\<dots> = ket a \<otimes>\<^sub>s ket (b + G a)" using H_G_same_upto_S[OF assms] that by auto
    also have "\<dots> = Uquery G *\<^sub>V ket a \<otimes>\<^sub>s ket b" using Uquery_ket by auto
    also have "\<dots> = (Uquery G o\<^sub>C\<^sub>L ?P \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket a \<otimes>\<^sub>s ket b"
      by (simp add: proj_classical_set_elem tensor_op_ell2 that)
    finally show ?thesis by auto
  qed
  moreover have "(Uquery H o\<^sub>C\<^sub>L ?P \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket a \<otimes>\<^sub>s ket b = 
    (Uquery G o\<^sub>C\<^sub>L ?P \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket a \<otimes>\<^sub>s ket b"
    if "S a"
    by (simp add: proj_classical_set_not_elem tensor_op_ell2 that)
  ultimately show ?case by (cases "S a", auto)
qed


lemma Uquery_G_H_same_on_not_S_embed:
  assumes "(H,G,S,z)\<in>carrier"
  shows "((X;Y) (Uquery H) o\<^sub>C\<^sub>L (not_S_embed S)) = ((X;Y) (Uquery G) o\<^sub>C\<^sub>L (not_S_embed S))"
proof -
  have "((X;Y) (Uquery H) o\<^sub>C\<^sub>L (not_S_embed S)) = 
    ((X;Y) (Uquery H) o\<^sub>C\<^sub>L (X;Y) (proj_classical_set (- (Collect S)) \<otimes>\<^sub>o id_cblinfun))"
    unfolding not_S_embed_def by (simp add: Laws_Quantum.register_pair_apply)
  also have "\<dots> = (X;Y) (Uquery H o\<^sub>C\<^sub>L proj_classical_set (- (Collect S)) \<otimes>\<^sub>o id_cblinfun)"
    by (simp add: Axioms_Quantum.register_mult) 
  also have "\<dots> = (X;Y) (Uquery G o\<^sub>C\<^sub>L proj_classical_set (- (Collect S)) \<otimes>\<^sub>o id_cblinfun)"
    using Uquery_G_H_same_on_not_S_embed' assms by auto
  also have "\<dots> = ((X;Y) (Uquery G) o\<^sub>C\<^sub>L (X;Y) (proj_classical_set (- (Collect S)) \<otimes>\<^sub>o id_cblinfun))"
    by (simp add: Axioms_Quantum.register_mult) 
  also have "\<dots> = ((X;Y) (Uquery G) o\<^sub>C\<^sub>L (not_S_embed S))"
    unfolding not_S_embed_def by (simp add: Laws_Quantum.register_pair_apply)
  finally show ?thesis by auto
qed

lemma Uquery_G_H_same_on_not_S_embed_tensor:
  assumes "(H,G,S,z)\<in>carrier"
  shows "((X_for_B;Y_for_B) (Uquery H) o\<^sub>C\<^sub>L Fst (not_S_embed S)) = 
 ((X_for_B;Y_for_B) (Uquery G) o\<^sub>C\<^sub>L Fst (not_S_embed S))"
  using Uquery_G_H_same_on_not_S_embed[OF assms] unfolding UqueryH_tensor_id_cblinfunB Fst_def 
  by (auto simp add: comp_tensor_op)



text \<open>Instantiations of mixed o2h locale for H and G\<close>


definition carrier_G where "carrier_G = (\<lambda>(H,G,S,z). (G,S,(H,z))) ` carrier"
definition distr_G where "distr_G = (\<lambda>(G,S,(H,z)). distr (H,G,S,z))"

lemma distr_G_pos: "\<forall>(G,S,z)\<in>carrier_G. distr_G (G,S,z) \<ge> 0"
  unfolding carrier_G_def distr_G_def using distr_pos by auto

lemma distr_G_sum_1: "(\<Sum>(G,S,z)\<in>carrier_G. distr_G (G,S,z)) = 1"
  unfolding carrier_G_def distr_G_def using distr_sum_1 
  by (subst sum.reindex, auto simp add: inj_on_def case_prod_beta)

lemma finite_carrier_G: "finite carrier_G" 
  unfolding carrier_G_def by (auto simp add: inj_on_def finite_carrier)


definition carrier_H where "carrier_H = (\<lambda>(H,G,S,z). (H,S,(G,z))) ` carrier"
definition distr_H where "distr_H = (\<lambda>(H,S,(G,z)). distr (H,G,S,z))"

lemma distr_H_pos: "\<forall>(H,S,z)\<in>carrier_H. distr_H (H,S,z) \<ge> 0"
  unfolding carrier_H_def distr_H_def using distr_pos by auto

lemma distr_H_sum_1: "(\<Sum>(H,S,z)\<in>carrier_H. distr_H (H,S,z)) = 1"
  unfolding carrier_H_def distr_H_def using distr_sum_1 
  by (subst sum.reindex[], auto simp add: inj_on_def case_prod_beta)

lemma finite_carrier_H: "finite carrier_H" 
  unfolding carrier_H_def by (auto simp add: inj_on_def finite_carrier)



interpretation mixed_H: mixed_o2h X Y d init flip bit valid empty carrier_H distr_H E P
  apply unfold_locales
  using distr_H_pos distr_H_sum_1 finite_carrier_H E_norm_id E_nonzero is_Proj_P
  by auto

interpretation mixed_G: mixed_o2h X Y d init flip bit valid empty carrier_G distr_G E P
  apply unfold_locales
  using distr_G_pos distr_G_sum_1 finite_carrier_G E_norm_id E_nonzero is_Proj_P
  by auto



text \<open>Lemmas on \<^const>\<open>Proj_ket_upto\<close> and \<open>run_adv_mixed\<close>. The adversary run upto i can be projected 
  to the first i ket states in the counting register.\<close>


lemma length_has_bits_upto:
  assumes "l\<in>has_bits_upto n"
  shows "length l = d"
  using assms unfolding has_bits_upto_def len_d_lists_def has_bits_def by auto


lemma empty_not_flip:
  assumes "x \<in> list_to_l ` has_bits_upto n" "n<d"
  shows "empty \<noteq> flip n x"    
proof -
  have "blog x" using assms using has_bits_upto_def surj_list_to_l by auto
  obtain l where x: "x = list_to_l l" and l_in:"l\<in>has_bits_upto n" using assms(1) by blast
  then have len: "length l = d" using length_has_bits_upto assms by auto
  have "\<not> l ! (length l - Suc n)" unfolding len using assms(2) has_bits_upto_elem l_in by auto
  then have "bit x n = bit empty n" unfolding x by (subst bit_list_to_l) (auto simp add: assms len)
  then have "bit (flip n x) n \<noteq> bit empty n" by (subst bit_flip_same[OF \<open>n<d\<close> \<open>blog x\<close>], auto)
  then show ?thesis by auto
qed

lemma empty_not_flip':
  assumes "x \<noteq> flip n empty" "n<d"
  shows "empty \<noteq> flip n x"    
proof (rule ccontr, safe)
  assume "empty = flip n x" 
  then have "flip n empty = flip n (flip n x)" by auto
  then have "flip n empty = x" by (metis assms(2) blog.intros(1) flip_flip not_blog_flip)
  then show False using assms by auto
qed


lemma Proj_ket_upto_Snd:
  "Proj_ket_upto A = Snd (proj_classical_set (list_to_l ` A))"
  unfolding Proj_ket_upto_def Proj_ket_set_def Snd_def by auto

lemma from_trace_class_tc_selfbutter:
  "from_trace_class (tc_selfbutter x) = selfbutter x"
  by (simp add: tc_butterfly.rep_eq tc_selfbutter_def)



lemma selfbutter_empty_US_Proj_ket_upto:
  assumes "i<d"
  shows "Snd (selfbutter (ket empty)) o\<^sub>C\<^sub>L ((US S i) o\<^sub>C\<^sub>L Proj_ket_upto (has_bits_upto i)) = 
  Fst (not_S_embed S) o\<^sub>C\<^sub>L Snd (selfbutter (ket empty))"
proof (intro equal_ket, safe, goal_cases)
  case (1 a b)
  have split_a: "ket a = S_embed S (ket a) + not_S_embed S (ket a)" 
    using S_embed_not_S_embed_add by auto
  have ?case (is "?left = ?right") if "b \<in> list_to_l ` has_bits_upto i" 
  proof -
    have "Proj (ccspan (ket ` list_to_l ` has_bits_upto i)) *\<^sub>V ket b = ket b" 
      using that by (simp add: Proj_fixes_image ccspan_superset')
    then have proj: "proj_classical_set (list_to_l ` has_bits_upto i) *\<^sub>V ket b = ket b"
      unfolding proj_classical_set_def by auto
    have "?left = (Snd (selfbutter (ket empty)) o\<^sub>C\<^sub>L (US S i)) *\<^sub>V ket (a, b)" 
      using proj by (auto simp add: Proj_ket_upto_def Proj_ket_set_def tensor_ell2_ket[symmetric] 
          tensor_op_ell2)
    also have "\<dots> = Snd (selfbutter (ket empty)) *\<^sub>V 
        ((S_embed S *\<^sub>V ket a) \<otimes>\<^sub>s (Ub i) *\<^sub>V ket b + ((not_S_embed S *\<^sub>V ket a) \<otimes>\<^sub>s ket b))" 
      using US_ket_split by auto
    also have "\<dots> = Snd (selfbutter (ket empty)) *\<^sub>V ((not_S_embed S *\<^sub>V ket a) \<otimes>\<^sub>s ket b)"
    proof -
      obtain bs where b: "bs\<in> has_bits_upto i" "b = list_to_l bs" 
        using \<open>b \<in> list_to_l ` has_bits_upto i\<close> by auto
      then have bs: "length bs = d" "\<not> (bs!(d-i-1))" unfolding has_bits_upto_def len_d_lists_def 
        using assms b(1) has_bits_upto_elem by auto
      then have "bit b i = bit empty i" unfolding b(2) 
        by (subst bit_list_to_l) (auto simp add: \<open>i<d\<close>)
      then have "flip i b \<noteq> empty" using assms bit_flip_same blog.intros(1) not_blog_flip by blast
      then have "Snd (selfbutter (ket empty)) *\<^sub>V ((S_embed S *\<^sub>V ket a) \<otimes>\<^sub>s (Ub i) *\<^sub>V ket b) = 0"
        by (simp add: Ub_def Snd_def classical_operator_ket[OF Ub_exists] tensor_op_ell2 
            tensor_ell2_scaleC2)
      then show ?thesis by (simp add: cblinfun.real.add_right)
    qed
      (*Compatibility of X is assumed!*)
    also have "\<dots> = ?right" unfolding Fst_def Snd_def
      by (auto simp add: tensor_ell2_ket[symmetric] cinner_ket tensor_op_ell2)
    finally show ?thesis by blast
  qed
  moreover have ?case (is "?left = ?right") if "\<not> (b \<in> list_to_l ` has_bits_upto i)" "blog b"
  proof -
    have "b \<noteq> empty" using that empty_list_to_l_has_bits_upto by force
    have "b \<notin> list_to_l ` has_bits_upto i" using that by auto
    then have proj: "proj_classical_set (list_to_l ` has_bits_upto i) *\<^sub>V ket b = 0"
      unfolding proj_classical_set_def by (intro Proj_0_compl, intro mem_ortho_ccspanI) auto
    then have "?left = 0" 
      by (auto simp add: Proj_ket_upto_def Proj_ket_set_def tensor_ell2_ket[symmetric] 
          tensor_op_ell2)
    moreover have "?right = 0" using  \<open>b \<noteq> empty\<close> unfolding Fst_def Snd_def
      by (auto simp add: tensor_ell2_ket[symmetric] cinner_ket tensor_op_ell2)
    ultimately show ?thesis by auto
  qed
  moreover have ?case (is "?left = ?right") if "\<not> blog b" 
  proof -
    have "b \<noteq> empty" using that blog.intros(1) by auto
    have "b \<notin> list_to_l ` has_bits_upto i"
      using has_bits_upto_def surj_list_to_l that by fastforce
    then have proj: "proj_classical_set (list_to_l ` has_bits_upto i) *\<^sub>V ket b = 0"
      unfolding proj_classical_set_def by (intro Proj_0_compl, intro mem_ortho_ccspanI) auto
    then have "?left = 0" 
      by (auto simp add: Proj_ket_upto_def Proj_ket_set_def tensor_ell2_ket[symmetric] 
          tensor_op_ell2)
    moreover have "?right = 0" using \<open>b \<noteq> empty\<close> unfolding Fst_def Snd_def
      by (auto simp add:  tensor_ell2_ket[symmetric] cinner_ket tensor_op_ell2)
    ultimately show ?thesis by auto
  qed
  ultimately show ?case by (cases "b \<in> list_to_l ` has_bits_upto i", auto)
qed




lemma list_to_l_has_bits_upto_flip:
  assumes "b \<in> list_to_l ` has_bits_upto n" "n<d"
  shows "flip n b \<in> list_to_l ` has_bits_upto (Suc n)"
proof -
  obtain lb where lb: "lb \<in> has_bits_upto n" and b: "b = list_to_l lb" using assms by blast
  then have len:"length lb = d" unfolding has_bits_upto_def len_d_lists_def by auto
  moreover have "\<not> lb ! (length lb - Suc n)" using lb assms(2) calculation has_bits_upto_elem 
    by auto 
  ultimately have flip: "flip n b = list_to_l (lb[length lb - Suc n := True])" 
    unfolding b by (subst flip_list_to_l) (auto simp add: assms)
  let ?lb' = "lb[length lb - Suc n := True]"
  have len_lb': "?lb' \<in> len_d_lists" unfolding len_d_lists_def using len by auto
  have "\<forall>i\<in>{Suc n..<d}. \<not> lb!(d-i-1)" using lb unfolding has_bits_upto_def has_bits_def by auto
  then have "\<forall>i\<in>{Suc n..<d}. \<not> ?lb'!(d-i-1)" unfolding len by fastforce
  then have "?lb' \<notin> has_bits {Suc n..<d}" unfolding has_bits_def by auto
  then have "?lb' \<in> has_bits_upto (Suc n)" using len_lb' unfolding has_bits_upto_def by auto
  then show ?thesis using flip by auto
qed


lemma Proj_ket_upto_US:
  assumes "n<d"
  shows "US S n o\<^sub>C\<^sub>L Proj_ket_upto (has_bits_upto n) = 
 Proj_ket_upto (has_bits_upto (Suc n)) o\<^sub>C\<^sub>L US S n o\<^sub>C\<^sub>L Proj_ket_upto (has_bits_upto n)"
proof (intro equal_ket, safe, goal_cases)
  case (1 a b)
  have split_a: "ket a = S_embed S (ket a) + not_S_embed S (ket a)" 
    using S_embed_not_S_embed_add by auto
  have ?case (is "?left = ?right") if "b \<in> list_to_l ` has_bits_upto n" 
  proof -
    have "Proj (ccspan (ket ` list_to_l ` has_bits_upto n)) *\<^sub>V ket b = ket b" 
      using that by (simp add: Proj_fixes_image ccspan_superset')
    then have Proj: "Proj_ket_upto (has_bits_upto n) *\<^sub>V ket (a,b) = ket (a,b)"
      unfolding proj_classical_set_def Proj_ket_upto_Snd Snd_def 
      by (auto simp add: tensor_op_ell2 tensor_ell2_ket[symmetric])
    have proj_Suc: "proj_classical_set (list_to_l ` has_bits_upto (Suc n)) *\<^sub>V ket b = ket b"
      unfolding proj_classical_set_def by (metis has_bits_upto_incl image_mono le_simps(1) 
          less_Suc_eq proj_classical_set_def proj_classical_set_elem subset_eq that)
    have proj_Suc_flip: "proj_classical_set (list_to_l ` has_bits_upto (Suc n)) *\<^sub>V ket (flip n b) = 
        ket (flip n b)"
      using list_to_l_has_bits_upto_flip[OF that \<open>n<d\<close>] by (auto simp add: proj_classical_set_elem)
    have "?left = US S n *\<^sub>V ket (a, b)" using Proj by auto
    also have "\<dots> = (S_embed S *\<^sub>V ket a) \<otimes>\<^sub>s ket (flip n b) + ((not_S_embed S *\<^sub>V ket a) \<otimes>\<^sub>s ket b)" 
      using US_ket_split Ub_ket by auto
    also have "\<dots> = ((S_embed S *\<^sub>V ket a) \<otimes>\<^sub>s 
      proj_classical_set (list_to_l ` has_bits_upto (Suc n)) *\<^sub>V ket (flip n b) + 
      ((not_S_embed S *\<^sub>V ket a) \<otimes>\<^sub>s proj_classical_set (list_to_l ` has_bits_upto (Suc n)) *\<^sub>V ket b))" 
      unfolding proj_Suc proj_Suc_flip by auto
    also have "\<dots> = (Proj_ket_upto (has_bits_upto (Suc n)) o\<^sub>C\<^sub>L US S n) *\<^sub>V ket (a,b)"
      unfolding Proj_ket_upto_Snd Snd_def US_def 
      by (auto simp add: tensor_op_ell2 cblinfun.add_right cblinfun.add_left tensor_ell2_ket[symmetric] 
          Ub_ket)
    also have "\<dots> = ?right" using Proj by auto
    finally show ?thesis by blast
  qed
  moreover have ?case (is "?left = ?right") if "\<not> (b \<in> list_to_l ` has_bits_upto n)"
  proof -
    have "b \<notin> list_to_l ` has_bits_upto n" using that by auto
    then have proj: "proj_classical_set (list_to_l ` has_bits_upto n) *\<^sub>V ket b = 0"
      unfolding proj_classical_set_def by (intro Proj_0_compl, intro mem_ortho_ccspanI) auto
    then have Proj:"Proj_ket_upto (has_bits_upto n) *\<^sub>V ket(a,b) = 0"
      unfolding Proj_ket_upto_Snd Snd_def by (auto simp add: tensor_ell2_ket[symmetric] tensor_op_ell2)
    then have "?left = 0" by auto
    moreover have "?right = 0"  using Proj by auto
    ultimately show ?thesis by auto
  qed
  ultimately show ?case by (cases "b \<in> list_to_l ` has_bits_upto n", auto)
qed


lemma run_pure_adv_projection:
  assumes "n<d+1" 
    and \<rho>: "\<rho> = run_pure_adv_tc n (\<lambda>m. if m<n+1 then Fst (UA m) else UB m) (US S) init_B X_for_B Y_for_B H"
  shows "sandwich_tc (Proj_ket_upto (has_bits_upto n)) \<rho> = \<rho>"
  using assms proof (induct n arbitrary: \<rho>)
  case 0
  let ?P = "proj_classical_set (list_to_l ` has_bits_upto 0)"
  have "sandwich (Snd ?P) (selfbutter init_B) = selfbutter init_B" 
    unfolding init_B_def Proj_ket_upto_Snd[symmetric]
    by (metis Proj_ket_upto_vec empty_list_has_bits_upto empty_list_to_l selfbutter_sandwich)
  then have "from_trace_class (sandwich_tc (Snd ?P) (tc_selfbutter init_B)) = 
    from_trace_class (tc_selfbutter init_B)"
    unfolding from_trace_class_sandwich_tc from_trace_class_tc_selfbutter by auto
  then have sand: "sandwich_tc (Snd ?P) (tc_selfbutter init_B) = tc_selfbutter init_B"
    using from_trace_class_inject by blast
  have *: "(if (0::nat)<0+1 then Fst (UA 0) else UB 0) = Fst (UA 0)" by auto 
  have "sandwich_tc (Proj_ket_upto (has_bits_upto 0)) \<rho> =
    sandwich_tc (Fst (UA 0)) (sandwich_tc (Snd ?P) (tc_selfbutter init_B))" 
    unfolding Proj_ket_upto_Snd 0 run_pure_adv_tc.simps(1) unfolding *
    by (metis Fst_def Snd_def from_trace_class_inject from_trace_class_sandwich_tc id_cblinfun.rep_eq 
        init_B_def from_trace_class_tc_selfbutter  selfbutter_sandwich tensor_op_ell2) 
  also have "\<dots> = sandwich_tc (Fst (UA 0)) (tc_selfbutter init_B)"
    unfolding sand by auto
  finally show ?case unfolding 0(2) by auto
next
  case (Suc n)
  define run where "run = run_pure_adv_tc n (\<lambda>m. if m<Suc n then Fst (UA m) else UB m) (US S) 
    init_B X_for_B Y_for_B H"
  have *: "(\<lambda>m. if m<(Suc n)+1 then Fst (UA m) else UB m) (Suc n) = Fst (UA (Suc n))" using Suc by auto
  have "n<d" "n<d+1" using Suc(2) by auto
  have rew: "(\<lambda>m. if m < Suc (Suc n) then Fst (UA m) else UB m) = 
    (\<lambda>m. if m < Suc n then Fst (UA m) else UB m)(Suc n:= Fst (UA(Suc n)))"
    by auto
  have over: "run_pure_adv_tc n (\<lambda>m. if m < Suc (Suc n) then Fst (UA m) else UB m) (US S) init_B
    X_for_B Y_for_B H = run" unfolding run_def rew by (intro run_pure_adv_tc_over) auto 
  have sand_run: "sandwich_tc (Proj_ket_upto (has_bits_upto n)) run = run" unfolding run_def
    by (subst Suc(1)[OF \<open>n<d+1\<close>]) auto
  have Suc': "sandwich_tc (Proj_ket_upto (has_bits_upto n)) run = run" 
    unfolding run_def using Suc \<open>n<d+1\<close> by auto
  have "\<rho> = sandwich_tc (Fst (UA (Suc n)) o\<^sub>C\<^sub>L (X_for_B;Y_for_B) (Uquery H) o\<^sub>C\<^sub>L US S n  o\<^sub>C\<^sub>L 
    Proj_ket_upto (has_bits_upto n)) run" 
    unfolding Suc(3) by (auto simp add: sand_run sandwich_tc_compose' \<open>n<d\<close> run_def[symmetric] over)
  also have "\<dots> = sandwich_tc (Fst (UA (Suc n)) o\<^sub>C\<^sub>L (X_for_B;Y_for_B) (Uquery H) o\<^sub>C\<^sub>L 
    (Proj_ket_upto (has_bits_upto (Suc n)) o\<^sub>C\<^sub>L US S n  o\<^sub>C\<^sub>L Proj_ket_upto (has_bits_upto n))) run" 
    using Proj_ket_upto_US[OF \<open>n<d\<close>] by (smt (verit, best) sandwich_tc_compose')
  also have "\<dots> = sandwich_tc (Fst (UA (Suc n)) o\<^sub>C\<^sub>L (X_for_B;Y_for_B) (Uquery H) o\<^sub>C\<^sub>L 
    Proj_ket_upto (has_bits_upto (Suc n)) o\<^sub>C\<^sub>L US S n) run" 
    by (auto simp add: sand_run sandwich_tc_compose')
  also have "\<dots> = sandwich_tc (Proj_ket_upto (has_bits_upto (Suc n)) o\<^sub>C\<^sub>L Fst (UA (Suc n)) o\<^sub>C\<^sub>L 
    ((X_for_B;Y_for_B) (Uquery H)) o\<^sub>C\<^sub>L US S n) run" 
    unfolding Proj_ket_upto_Snd Snd_def UqueryH_tensor_id_cblinfunB Fst_def 
    by (auto simp add: comp_tensor_op sandwich_tc_compose')
  also have "\<dots> = sandwich_tc (Proj_ket_upto (has_bits_upto (Suc n))) \<rho>"
    unfolding Suc(3) by (auto simp add: sand_run sandwich_tc_compose' Suc \<open>n<d\<close> run_def[symmetric] over)
  finally show ?case by auto
qed


lemma run_mixed_adv_projection_finite:
  assumes "\<And>i. i < n + 1 \<Longrightarrow> finite (Rep_kraus_family (kf_Fst (F i)::
    (('mem \<times> 'l) ell2, ('mem \<times> 'l) ell2, unit) kraus_family))"
    and "\<And>i. i < n + 1 \<Longrightarrow> fst ` Rep_kraus_family (kf_Fst (F i)::
    (('mem \<times> 'l) ell2, ('mem \<times> 'l) ell2, unit) kraus_family) \<noteq> {}"
  assumes "n<d+1"
  shows "sandwich_tc (Proj_ket_upto (has_bits_upto n)) 
  (run_mixed_adv n (\<lambda>n. kf_Fst (F n)) (US S) init_B X_for_B Y_for_B H) = 
  run_mixed_adv n (\<lambda>n. kf_Fst (F n)) (US S) init_B X_for_B Y_for_B H"
proof -
  have "sandwich_tc (Proj_ket_upto (has_bits_upto n)) 
    (run_pure_adv_tc n x (US S) init_B X_for_B Y_for_B H) =
    run_pure_adv_tc n x (US S) init_B X_for_B Y_for_B H" 
    if "x \<in> purify_comp_kraus n (\<lambda>n. kf_Fst (F n))" for x
  proof -
    have *: "(\<And>i. i < n + 1 \<Longrightarrow> fst ` Rep_kraus_family (F i) \<noteq> {})" 
      using assms(2) unfolding fst_Rep_kf_Fst by auto
    obtain UA where x:"x = (\<lambda>a. if a < n+1 then Fst (UA a) else undefined)" using 
        purification_kf_Fst[OF * \<open>x \<in> purify_comp_kraus n (\<lambda>n. kf_Fst (F n))\<close>]
      by auto
    show ?thesis using assms by (intro run_pure_adv_projection[of n _ UA "(\<lambda>_. undefined)" S H]) 
        (auto simp add: x)
  qed
  then show ?thesis by (subst purification_run_mixed_adv[OF assms(1,2)], simp, 
        subst purification_run_mixed_adv[OF assms(1,2)], simp)
      (use assms in \<open>auto simp add: sandwich_tc_sum intro!: sum.cong\<close>)
qed


lemma run_mixed_adv_projection:
  assumes "\<And>i. i < d + 1 \<Longrightarrow> fst ` Rep_kraus_family (kf_Fst (F i)::
    (('mem \<times> 'l) ell2, ('mem \<times> 'l) ell2, unit) kraus_family) \<noteq> {}"
  assumes "n<d+1"
  shows "sandwich_tc (Proj_ket_upto (has_bits_upto n)) 
  (run_mixed_adv n (\<lambda>n. kf_Fst (F n)) (US S) init_B X_for_B Y_for_B H) = 
  run_mixed_adv n (\<lambda>n. kf_Fst (F n)) (US S) init_B X_for_B Y_for_B H"
proof -
  define \<rho> where "\<rho> = run_mixed_adv n (\<lambda>n. kf_Fst (F n)) (US S) init_B X_for_B Y_for_B H"
  define \<rho>sum where 
    "\<rho>sum F' = run_mixed_adv n (\<lambda>n. kf_Fst (F' n)) (US S) init_B X_for_B Y_for_B H" for F'
  have \<rho>_has_sum': "((\<lambda>F'. run_mixed_adv n F' (US S) init_B X_for_B Y_for_B H) has_sum \<rho>)
     (finite_kraus_subadv (\<lambda>m. kf_Fst (F m)) n)"
    unfolding \<rho>_def using run_mixed_adv_has_sum by blast
  then have \<rho>_has_sum: "(\<rho>sum has_sum \<rho>) (finite_kraus_subadv F n)" 
  proof -
    have inj: "inj_on (\<lambda>f. \<lambda>n\<in>{0..<n+1}. kf_Fst (f n)) (finite_kraus_subadv F n)" 
      using inj_on_kf_Fst by auto
    have rew: "\<rho>sum = (\<lambda>f. run_mixed_adv n f (US S) init_B X_for_B Y_for_B H) o 
      (\<lambda>f. \<lambda>n\<in>{0..<n+1}. kf_Fst (f n))" unfolding \<rho>sum_def
      using run_mixed_adv_kf_Fst_restricted[where init' = init_B and X' = X_for_B and Y'=Y_for_B] 
      by auto
    show ?thesis unfolding rew  by (subst has_sum_reindex[OF inj, symmetric]) 
        (unfold finite_kraus_subadv_Fst_invert[symmetric], rule \<rho>_has_sum')
  qed
  have elem: "(sandwich_tc (Proj_ket_upto (has_bits_upto n)) o \<rho>sum) x = \<rho>sum x" 
    if "x \<in> (finite_kraus_subadv F n)" for x unfolding \<rho>sum_def o_def
  proof (intro run_mixed_adv_projection_finite, goal_cases)
    case (1 i)
    then show ?case using finite_kf_Fst[OF fin_subadv_fin_Rep_kraus_family[OF that]] assms 
      by auto
  next
    case (2 i)
    then show ?case using fin_subadv_nonzero[OF that] assms 
      unfolding fst_Rep_kf_Fst by auto
  qed (use assms in \<open>auto\<close>)
  have sand_has_sum_rho: "(sandwich_tc (Proj_ket_upto (has_bits_upto n)) o \<rho>sum has_sum \<rho>) 
    (finite_kraus_subadv (F) n)" 
    by (subst has_sum_cong[where g = \<rho>sum]) (use elem \<rho>_has_sum in \<open>auto\<close>)
  have sand_has_sum_sand: "(sandwich_tc (Proj_ket_upto (has_bits_upto n)) o \<rho>sum has_sum 
    (sandwich_tc (Proj_ket_upto (has_bits_upto n)) \<rho>)) 
    (finite_kraus_subadv (F) n)" by (intro sandwich_tc_has_sum[OF \<rho>_has_sum])
  have "sandwich_tc (Proj_ket_upto (has_bits_upto n)) \<rho> = \<rho>" 
    using has_sum_unique[OF sand_has_sum_sand sand_has_sum_rho] by auto
  then show ?thesis unfolding \<rho>_def by auto
qed






text \<open>Lemmas of commutation with non-Find event\<close>


lemma Proj_commutes_with_Uquery:
  "Snd (selfbutter (ket empty)) o\<^sub>C\<^sub>L (X_for_B;Y_for_B) (Uquery G) =
 (X_for_B;Y_for_B) (Uquery G) o\<^sub>C\<^sub>L Snd (selfbutter (ket empty))"
  unfolding Snd_def by (simp add: UqueryH_tensor_id_cblinfunB comp_tensor_op) 


lemma run_mixed_adv_G_H_same:
  assumes "(H,G,S,z)\<in>carrier" "n<d+1"
  shows "sandwich_tc (Snd (selfbutter (ket empty))) 
    (run_mixed_adv n (\<lambda>n. kf_Fst (E n)) (US S) init_B X_for_B Y_for_B H) =
  sandwich_tc (Snd (selfbutter (ket empty)))
    (run_mixed_adv n (\<lambda>n. kf_Fst (E n)) (US S) init_B X_for_B Y_for_B G)"
  using assms(2) proof (induct n)
  case (Suc n)
  have "n<d" "n<Suc d" using Suc by auto
  let ?P = "Snd (selfbutter (ket empty))"
  let ?P' = "Proj_ket_upto (has_bits_upto n)"
  let ?\<rho> = "(\<lambda>x Y. (run_mixed_adv x (\<lambda>n. kf_Fst (E n)) (US S) init_B X_for_B Y_for_B Y))"
  have "sandwich_tc ?P (?\<rho> (Suc n) H) = kf_apply (kf_Fst (E (Suc n)))
    (sandwich_tc (?P o\<^sub>C\<^sub>L (X_for_B;Y_for_B) (Uquery H) o\<^sub>C\<^sub>L US S n) (?\<rho> n H))"
    using sandwich_tc_kf_apply_Fst by (auto simp add: sandwich_tc_compose')
  also have "\<dots> = kf_apply (kf_Fst (E (Suc n)))
    (sandwich_tc ((X_for_B;Y_for_B) (Uquery H) o\<^sub>C\<^sub>L ?P o\<^sub>C\<^sub>L US S n o\<^sub>C\<^sub>L ?P') (?\<rho> n H))"
    by (subst Proj_commutes_with_Uquery, subst run_mixed_adv_projection[symmetric])
      (auto simp add: Fst_E_nonzero sandwich_tc_compose' \<open>n<Suc d\<close>)
  also have "\<dots> = kf_apply (kf_Fst (E (Suc n)))
    (sandwich_tc ((X_for_B;Y_for_B) (Uquery H) o\<^sub>C\<^sub>L Fst (not_S_embed S) o\<^sub>C\<^sub>L ?P) (?\<rho> n H))"
    using selfbutter_empty_US_Proj_ket_upto[OF \<open>n<d\<close>]
    by (metis (no_types, lifting) sandwich_tc_compose')
  also have "\<dots> = kf_apply (kf_Fst (E (Suc n)))
    (sandwich_tc ((X_for_B;Y_for_B) (Uquery G) o\<^sub>C\<^sub>L Fst (not_S_embed S) o\<^sub>C\<^sub>L ?P) (?\<rho> n H))"
    using Uquery_G_H_same_on_not_S_embed_tensor assms by auto
  also have "\<dots> = kf_apply (kf_Fst (E (Suc n)))
    (sandwich_tc ((X_for_B;Y_for_B) (Uquery G) o\<^sub>C\<^sub>L Fst (not_S_embed S) o\<^sub>C\<^sub>L ?P) (?\<rho> n G))"
    using Suc by (auto simp add: sandwich_tc_compose')
  also have "\<dots> = kf_apply (kf_Fst (E (Suc n)))
    (sandwich_tc ((X_for_B;Y_for_B) (Uquery G) o\<^sub>C\<^sub>L ?P o\<^sub>C\<^sub>L US S n o\<^sub>C\<^sub>L ?P') (?\<rho> n G))"
    using selfbutter_empty_US_Proj_ket_upto[OF \<open>n<d\<close>]
    by (metis (no_types, lifting) sandwich_tc_compose')
  also have "\<dots> = kf_apply (kf_Fst (E (Suc n)))
    (sandwich_tc (?P o\<^sub>C\<^sub>L (X_for_B;Y_for_B) (Uquery G) o\<^sub>C\<^sub>L US S n) (?\<rho> n G))" 
    by (subst Proj_commutes_with_Uquery, subst (2) run_mixed_adv_projection[symmetric])
      (auto simp add: Fst_E_nonzero sandwich_tc_compose' \<open>n<Suc d\<close>)
  also have "\<dots> = sandwich_tc ?P (?\<rho> (Suc n) G)"
    using sandwich_tc_kf_apply_Fst[symmetric] by (auto simp add: sandwich_tc_compose')
  finally show ?case by auto
qed auto


lemma run_mixed_B_G_H_same:
  assumes "(H,G,S,z)\<in>carrier"
  shows "sandwich_tc (Q \<otimes>\<^sub>o selfbutter (ket empty)) (run_mixed_B E H S) = 
sandwich_tc (Q \<otimes>\<^sub>o selfbutter (ket empty)) (run_mixed_B E G S)"
proof -
  have "sandwich_tc (Q \<otimes>\<^sub>o selfbutter (ket empty)) (run_mixed_B E H S) =
    sandwich_tc (Q \<otimes>\<^sub>o id_cblinfun) (sandwich_tc (Snd (selfbutter (ket empty)))
     (run_mixed_adv d (\<lambda>n. kf_Fst (E n)) (US S) init_B X_for_B Y_for_B H))"
    unfolding run_mixed_B_def 
    by (auto simp add: sandwich_tc_compose'[symmetric] Snd_def comp_tensor_op)
  also have "\<dots>  = sandwich_tc (Q \<otimes>\<^sub>o id_cblinfun) (sandwich_tc (Snd (selfbutter (ket empty)))
     (run_mixed_adv d (\<lambda>n. kf_Fst (E n)) (US S) init_B X_for_B Y_for_B G))"
    using run_mixed_adv_G_H_same[where n=d, OF assms] by auto
  also have "\<dots> = sandwich_tc (Q \<otimes>\<^sub>o selfbutter (ket empty)) (run_mixed_B E G S)"
    unfolding run_mixed_B_def 
    by (auto simp add: sandwich_tc_compose'[symmetric] Snd_def comp_tensor_op)
  finally show ?thesis by auto
qed



lemma \<rho>right_G_H_same:
  "sandwich_tc (Q \<otimes>\<^sub>o selfbutter (ket empty)) (mixed_H.\<rho>right E) = 
 sandwich_tc (Q \<otimes>\<^sub>o selfbutter (ket empty)) (mixed_G.\<rho>right E)"
proof -
  have "sandwich_tc (Q \<otimes>\<^sub>o selfbutter (ket empty)) (mixed_H.\<rho>right E) = 
    (\<Sum>(H,G,S,z)\<in>carrier. distr (H,G,S,z) *\<^sub>C 
    sandwich_tc (Q \<otimes>\<^sub>o selfbutter (ket empty)) (run_mixed_B E H S))"
    unfolding mixed_H.\<rho>right_def unfolding carrier_H_def distr_H_def 
    by (subst sum.reindex) (auto simp add: inj_on_def case_prod_beta sandwich_tc_sum 
        sandwich_tc_scaleC_right intro!: sum.cong)
  also have "\<dots> = (\<Sum>(H,G,S,z)\<in>carrier. distr (H,G,S,z) *\<^sub>C 
    sandwich_tc (Q \<otimes>\<^sub>o selfbutter (ket empty)) (run_mixed_B E G S))"
    using run_mixed_B_G_H_same  by (auto intro!: sum.cong)
  also have "\<dots> = sandwich_tc (Q \<otimes>\<^sub>o selfbutter (ket empty)) (mixed_G.\<rho>right E)" 
    unfolding mixed_G.\<rho>right_def unfolding carrier_G_def distr_G_def 
    by (subst sum.reindex) (auto simp add: inj_on_def case_prod_beta sandwich_tc_sum 
        sandwich_tc_scaleC_right intro!: sum.cong)
  finally show ?thesis by auto
qed

lemma trace_compose_tcr_H_G_same:
  "trace_tc (compose_tcr (Snd (selfbutter (ket empty))) (mixed_H.\<rho>right E)) =
 trace_tc (compose_tcr (Snd (selfbutter (ket empty))) (mixed_G.\<rho>right E))"
proof -
  have "trace (from_trace_class
    (compose_tcr (Snd (selfbutter (ket empty))) (mixed_H.\<rho>right E)) o\<^sub>C\<^sub>L (Snd (selfbutter (ket empty)))*) =
    trace (from_trace_class
    (compose_tcr (Snd (selfbutter (ket empty))) (mixed_G.\<rho>right E)) o\<^sub>C\<^sub>L (Snd (selfbutter (ket empty)))*)" 
    by (metis (no_types, opaque_lifting) Snd_def \<rho>right_G_H_same compose_tcr.rep_eq 
        from_trace_class_sandwich_tc sandwich_apply)
  then have "trace (from_trace_class
    (compose_tcr (Snd (selfbutter (ket empty))) (mixed_H.\<rho>right E))) =
    trace (from_trace_class
    (compose_tcr (Snd (selfbutter (ket empty))) (mixed_G.\<rho>right E)))" 
    by (smt (verit, best) Snd_def butterfly_is_Proj cblinfun_assoc_left(1) circularity_of_trace 
        compose_tcr.rep_eq is_Proj_algebraic is_Proj_id is_Proj_tensor_op norm_ket 
        trace_class_from_trace_class)
  then show ?thesis unfolding trace_tc.rep_eq by auto
qed



text \<open>The probability of not Find and the adversary succeeding for H\S and G\S are the same.
$Pr [b \and \not Find:b\leftarrow A^{H\backslash S}(z)] = 
 Pr [b \and \not Find:b\leftarrow A^{G\backslash S}(z)]$\<close>

lemma Pright_G_H_same:
  "mixed_H.Pright (Q \<otimes>\<^sub>o selfbutter (ket empty)) = mixed_G.Pright (Q \<otimes>\<^sub>o selfbutter (ket empty))"
  unfolding mixed_H.Pright_def mixed_G.Pright_def mixed_G.PM_altdef 
  using \<rho>right_G_H_same[where Q = Q] by auto




text \<open>The finding event occurs with the same probability for G and H 
if the overall norm stays the same.\<close>

lemma Pfind_G_H_same:
  assumes "norm (mixed_H.\<rho>right E) = norm (mixed_G.\<rho>right E)"
  shows "mixed_H.Pfind E = mixed_G.Pfind E"
proof -
  have "mixed_H.Pfind E = trace_tc (compose_tcr 
  (id_cblinfun - Snd (selfbutter (ket empty))::('mem\<times>'l) update) (mixed_H.\<rho>right E))"
    unfolding mixed_H.Pfind_def mixed_G.end_measure_def Snd_def 
    by (auto simp add: tensor_op_right_minus)
  also have "\<dots> = trace_tc (mixed_H.\<rho>right E) - 
    trace_tc (compose_tcr (Snd (selfbutter (ket empty))) (mixed_H.\<rho>right E))"
    by (simp add: compose_tcr.diff_left trace_tc_minus)
  also have "\<dots> = norm (mixed_H.\<rho>right E) -
    trace_tc (compose_tcr (Snd (selfbutter (ket empty))) (mixed_H.\<rho>right E))"
    by (simp add: mixed_H.\<rho>right_pos norm_tc_pos)
  also have  "\<dots> = norm (mixed_G.\<rho>right E) -
    trace_tc (compose_tcr (Snd (selfbutter (ket empty))) (mixed_G.\<rho>right E))"
    unfolding assms using trace_compose_tcr_H_G_same by auto
  also have "\<dots> = trace_tc (mixed_G.\<rho>right E) - 
    trace_tc (compose_tcr (Snd (selfbutter (ket empty))) (mixed_G.\<rho>right E))"
    by (simp add: mixed_G.\<rho>right_pos norm_tc_pos)
  also have "\<dots> = trace_tc (compose_tcr 
  (id_cblinfun - Snd (selfbutter (ket empty))::('mem\<times>'l) update) (mixed_G.\<rho>right E))"
    by (simp add: compose_tcr.diff_left trace_tc_minus)
  also have "\<dots> = mixed_G.Pfind E"
    unfolding mixed_G.Pfind_def mixed_G.end_measure_def Snd_def 
    by (auto simp add: tensor_op_right_minus)
  finally show ?thesis by auto
qed

lemma Pfind_G_H_same_nonterm:
  shows "(mixed_H.Pfind E - mixed_G.Pfind E) = 
  (norm (mixed_H.\<rho>right E) - norm (mixed_G.\<rho>right E))"
proof -
  have "mixed_H.Pfind E = trace_tc (compose_tcr 
  (id_cblinfun - Snd (selfbutter (ket empty))::('mem\<times>'l) update) (mixed_H.\<rho>right E))"
    unfolding mixed_H.Pfind_def mixed_G.end_measure_def Snd_def 
    by (auto simp add: tensor_op_right_minus)
  also have "\<dots> = trace_tc (mixed_H.\<rho>right E) - 
    trace_tc (compose_tcr (Snd (selfbutter (ket empty))) (mixed_H.\<rho>right E))"
    by (simp add: compose_tcr.diff_left trace_tc_minus)
  also have "\<dots> = norm (mixed_H.\<rho>right E) -
    trace_tc (compose_tcr (Snd (selfbutter (ket empty))) (mixed_H.\<rho>right E))"
    by (simp add: mixed_H.\<rho>right_pos norm_tc_pos)
  finally have H: "mixed_H.Pfind E = norm (mixed_H.\<rho>right E) -
    trace_tc (compose_tcr (Snd (selfbutter (ket empty))) (mixed_G.\<rho>right E))"
    using trace_compose_tcr_H_G_same by auto
  have "mixed_G.Pfind E = trace_tc (compose_tcr 
  (id_cblinfun - Snd (selfbutter (ket empty))::('mem\<times>'l) update) (mixed_G.\<rho>right E))"
    unfolding mixed_G.Pfind_def mixed_G.end_measure_def Snd_def 
    by (auto simp add: tensor_op_right_minus)
  also have "\<dots> = trace_tc (mixed_G.\<rho>right E) - 
    trace_tc (compose_tcr (Snd (selfbutter (ket empty))) (mixed_G.\<rho>right E))"
    by (simp add: compose_tcr.diff_left trace_tc_minus)
  finally have G: "mixed_G.Pfind E = norm (mixed_G.\<rho>right E) -
    trace_tc (compose_tcr (Snd (selfbutter (ket empty))) (mixed_G.\<rho>right E))"
    by (simp add: mixed_G.\<rho>right_pos norm_tc_pos)
  show ?thesis unfolding H G using complex_of_real_abs by auto
qed



text \<open>The general version of the O2H with non-termination part.\<close>

theorem mixed_o2h_nonterm:
  shows 
    "\<bar>mixed_H.Pleft P - mixed_G.Pleft P\<bar> \<le>  
  2 * sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)
+ 2 * sqrt ((d+1) * Re (mixed_G.Pfind E) + d* mixed_G.P_nonterm E)"
    and 
    "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_G.Pleft P)\<bar> \<le> 
  sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)
+ sqrt ((d+1) * Re (mixed_G.Pfind E) + d* mixed_G.P_nonterm E)"
proof -
  let ?P = "P \<otimes>\<^sub>o selfbutter (ket empty)"
  have norm_P: "norm ?P \<le> 1"
    by (simp add: butterfly_is_Proj is_Proj_tensor_op mixed_G.is_Proj_P norm_is_Proj)
  have "\<bar>mixed_H.Pleft P - mixed_G.Pleft P\<bar> = 
    \<bar>mixed_H.Pleft' ?P - mixed_H.Pright ?P + mixed_G.Pright ?P - mixed_G.Pleft' ?P\<bar>"
    using Pright_G_H_same unfolding mixed_G.Pleft_Pleft'_empty mixed_H.Pleft_Pleft'_empty by auto
  also have "\<dots>  \<le> \<bar>mixed_H.Pleft' ?P - mixed_H.Pright ?P\<bar> + 
    \<bar>mixed_G.Pleft' ?P - mixed_G.Pright ?P\<bar>" by linarith
  also have "\<dots> \<le>  2 * sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E) + 
    2 * sqrt ((d+1) * Re (mixed_G.Pfind E) + d* mixed_G.P_nonterm E)"
    using mixed_H.estimate_Pfind[OF norm_P] mixed_G.estimate_Pfind[OF norm_P] 
    by auto
  finally show "\<bar>mixed_H.Pleft P - mixed_G.Pleft P\<bar> \<le>  
     2 * sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)
   + 2 * sqrt ((d+1) * Re (mixed_G.Pfind E) + d* mixed_G.P_nonterm E)"
    by auto
  have "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_G.Pleft P)\<bar> = 
    \<bar>sqrt (mixed_H.Pleft' ?P) - sqrt (mixed_H.Pright ?P) + 
    sqrt (mixed_G.Pright ?P) - sqrt (mixed_G.Pleft' ?P)\<bar>"
    using Pright_G_H_same unfolding mixed_G.Pleft_Pleft'_empty mixed_H.Pleft_Pleft'_empty by auto
  also have "\<dots>  \<le> \<bar>sqrt (mixed_H.Pleft' ?P) - sqrt (mixed_H.Pright ?P)\<bar> + 
    \<bar>sqrt (mixed_G.Pleft' ?P) - sqrt (mixed_G.Pright ?P)\<bar>" by linarith
  also have "\<dots> \<le> sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)
    + sqrt ((d+1) * Re (mixed_G.Pfind E) + d* mixed_G.P_nonterm E)"
    using mixed_H.estimate_Pfind_sqrt[OF norm_P] mixed_G.estimate_Pfind_sqrt[OF norm_P] 
    by auto
  finally show "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_G.Pleft P)\<bar> \<le> 
      sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)
    + sqrt ((d+1) * Re (mixed_G.Pfind E) + d* mixed_G.P_nonterm E)"
    by auto
qed

text \<open>The general version of the O2H with terminating adversary. This formulation corresponds to 
Theorem 1.\<close>

theorem mixed_o2h_term:
  assumes "\<And>i. i<d+1 \<Longrightarrow> km_trace_preserving (kf_apply (E i))"
  shows 
    "\<bar>mixed_H.Pleft P - mixed_G.Pleft P\<bar> \<le>  4 * sqrt ((d+1) * Re (mixed_H.Pfind E))"
    and 
    "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_G.Pleft P)\<bar> \<le>  2 * sqrt ((d+1) * Re (mixed_H.Pfind E))"
proof -
  have normHright: "norm (mixed_H.\<rho>right E) = 1" 
    by (rule mixed_H.trace_preserving_norm_\<rho>right[OF trace_preserving_kf_Fst[OF assms]])
  have normHcount: "norm (mixed_H.\<rho>count E) = 1" 
    by (rule mixed_H.trace_preserving_norm_\<rho>count[OF trace_preserving_kf_Fst[OF assms]])
  have normGright: "norm (mixed_G.\<rho>right E) = 1" 
    by (rule mixed_G.trace_preserving_norm_\<rho>right[OF trace_preserving_kf_Fst[OF assms]])
  have normGcount: "norm (mixed_G.\<rho>count E) = 1" 
    by (rule mixed_G.trace_preserving_norm_\<rho>count[OF trace_preserving_kf_Fst[OF assms]])
  have norm: "norm (mixed_H.\<rho>right E) = norm (mixed_G.\<rho>right E)" using normHright normGright by auto
  have terminH: "mixed_H.P_nonterm E = 0" 
    unfolding mixed_H.P_nonterm_def using normHright normHcount 
    by (metis cmod_Re complex_of_real_nn_iff mixed_H.\<rho>count_pos mixed_H.\<rho>right_pos norm_le_zero_iff 
        norm_pths(2) norm_tc_pos norm_zero of_real_0)
  have terminG: "mixed_G.P_nonterm E = 0" 
    unfolding mixed_G.P_nonterm_def using normGright normGcount 
    by (smt (verit, del_insts) Re_complex_of_real mixed_G.\<rho>count_pos mixed_G.\<rho>right_pos norm_eq_zero 
        norm_le_zero_iff norm_of_real norm_pths(2) norm_tc_pos)
  show "\<bar>mixed_H.Pleft P - mixed_G.Pleft P\<bar> \<le>  4 * sqrt ((d+1) * Re (mixed_H.Pfind E))"
    using mixed_o2h_nonterm(1) Pfind_G_H_same[OF norm] terminH terminG by auto
  show "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_G.Pleft P)\<bar> \<le>  2 * sqrt ((d+1) * Re (mixed_H.Pfind E))"
    using mixed_o2h_nonterm(2) Pfind_G_H_same[OF norm] terminH terminG by auto
qed



text \<open>Other formulations of the mixed o2h.\<close>

text \<open>Theorem 1, definition of Pright (2)\<close>

definition Proj_2  :: "('mem \<times> 'l) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('mem \<times> 'l) ell2" where
  "Proj_2 = P \<otimes>\<^sub>o id_cblinfun"

lemma norm_Proj_2:
  "norm Proj_2 \<le> 1"
  unfolding Proj_2_def using mixed_H.norm_P by (simp add: tensor_op_norm)

theorem mixed_o2h_nonterm_2:
  shows 
    "\<bar>mixed_H.Pleft P - mixed_H.Pright Proj_2\<bar> \<le>  
  2 * sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    and 
    "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_H.Pright Proj_2)\<bar> \<le> 
  sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
proof -
  have "\<bar>mixed_H.Pleft P - mixed_H.Pright Proj_2\<bar> = 
    \<bar>mixed_H.Pleft' Proj_2 - mixed_H.Pright Proj_2\<bar>"
    unfolding mixed_H.Pleft_Pleft'_id Proj_2_def by auto
  also have "\<dots> \<le>  2 * sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    using mixed_H.estimate_Pfind[OF norm_Proj_2] by auto
  finally show "\<bar>mixed_H.Pleft P - mixed_H.Pright Proj_2\<bar> \<le>  
    2 * sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    by auto
  have "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_H.Pright Proj_2)\<bar> = 
    \<bar>sqrt (mixed_H.Pleft' Proj_2) - sqrt (mixed_H.Pright Proj_2)\<bar>"
    unfolding mixed_H.Pleft_Pleft'_id Proj_2_def by auto
  also have "\<dots> \<le> sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    using mixed_H.estimate_Pfind_sqrt[OF norm_Proj_2] by auto
  finally show "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_H.Pright Proj_2)\<bar> \<le> 
    sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    by auto
qed

theorem mixed_o2h_term_2:
  assumes "\<And>i. i<d+1 \<Longrightarrow> km_trace_preserving (kf_apply (E i))"
  shows 
    "\<bar>mixed_H.Pleft P - mixed_H.Pright Proj_2\<bar> \<le> 
  2 * sqrt ((d+1) * Re (mixed_H.Pfind E))"
    and 
    "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_H.Pright Proj_2)\<bar> \<le> 
  sqrt ((d+1) * Re (mixed_H.Pfind E))"
proof -
  have normHright: "norm (mixed_H.\<rho>right E) = 1" 
    by (rule mixed_H.trace_preserving_norm_\<rho>right[OF trace_preserving_kf_Fst[OF assms]])
  have normHcount: "norm (mixed_H.\<rho>count E) = 1" 
    by (rule mixed_H.trace_preserving_norm_\<rho>count[OF trace_preserving_kf_Fst[OF assms]])
  have terminH: "mixed_H.P_nonterm E = 0" 
    unfolding mixed_H.P_nonterm_def using normHright normHcount 
    by (metis cmod_Re complex_of_real_nn_iff mixed_H.\<rho>count_pos mixed_H.\<rho>right_pos norm_le_zero_iff 
        norm_pths(2) norm_tc_pos norm_zero of_real_0)
  show "\<bar>mixed_H.Pleft P - mixed_H.Pright Proj_2\<bar> \<le> 
    2 * sqrt ((d+1) * Re (mixed_H.Pfind E))"
    using mixed_o2h_nonterm_2(1) terminH by auto
  show "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_H.Pright Proj_2)\<bar> \<le> 
    sqrt ((d+1) * Re (mixed_H.Pfind E))"
    using mixed_o2h_nonterm_2(2) terminH by auto
qed


text \<open>Theorem 1, definition of Pright (3)\<close>


definition Proj_3  :: "('mem \<times> 'l) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('mem \<times> 'l) ell2" where
  "Proj_3 = P \<otimes>\<^sub>o selfbutter (ket empty)"

lemma is_Proj_3:
  "is_Proj Proj_3"
  unfolding Proj_3_def 
  by (simp add: butterfly_is_Proj is_Proj_tensor_op mixed_G.is_Proj_P)

lemma Proj_3_altdef:
  "Proj_3 = Proj ((P \<otimes>\<^sub>o id_cblinfun) *\<^sub>S \<top> \<squnion> (id_cblinfun \<otimes>\<^sub>o selfbutter (ket empty)) *\<^sub>S \<top>)"
  oops

lemma norm_Proj_3:
  "norm Proj_3 \<le> 1"
  unfolding Proj_3_def using mixed_H.norm_P by (simp add: norm_butterfly tensor_op_norm)

theorem mixed_o2h_nonterm_3:
  shows 
    "\<bar>mixed_H.Pleft P - mixed_H.Pright Proj_3\<bar> \<le>  
  2 * sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    and 
    "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_H.Pright Proj_3)\<bar> \<le> 
  sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
proof -
  have "\<bar>mixed_H.Pleft P - mixed_H.Pright Proj_3\<bar> = 
    \<bar>mixed_H.Pleft' Proj_3 - mixed_H.Pright Proj_3\<bar>"
    unfolding mixed_H.Pleft_Pleft'_empty Proj_3_def by auto
  also have "\<dots> \<le>  2 * sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    using mixed_H.estimate_Pfind[OF norm_Proj_3] by auto
  finally show "\<bar>mixed_H.Pleft P - mixed_H.Pright Proj_3\<bar> \<le>  
    2 * sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    by auto
  have "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_H.Pright Proj_3)\<bar> = 
    \<bar>sqrt (mixed_H.Pleft' Proj_3) - sqrt (mixed_H.Pright Proj_3)\<bar>"
    unfolding mixed_H.Pleft_Pleft'_empty Proj_3_def by auto
  also have "\<dots> \<le> sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    using mixed_H.estimate_Pfind_sqrt[OF norm_Proj_3] by auto
  finally show "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_H.Pright Proj_3)\<bar> \<le> 
    sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    by auto
qed

theorem mixed_o2h_term_3:
  assumes "\<And>i. i<d+1 \<Longrightarrow> km_trace_preserving (kf_apply (E i))"
  shows 
    "\<bar>mixed_H.Pleft P - mixed_H.Pright Proj_3\<bar> \<le> 
  2 * sqrt ((d+1) * Re (mixed_H.Pfind E))"
    and 
    "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_H.Pright Proj_3)\<bar> \<le> 
  sqrt ((d+1) * Re (mixed_H.Pfind E))"
proof -
  have normHright: "norm (mixed_H.\<rho>right E) = 1" 
    by (rule mixed_H.trace_preserving_norm_\<rho>right[OF trace_preserving_kf_Fst[OF assms]])
  have normHcount: "norm (mixed_H.\<rho>count E) = 1" 
    by (rule mixed_H.trace_preserving_norm_\<rho>count[OF trace_preserving_kf_Fst[OF assms]])
  have terminH: "mixed_H.P_nonterm E = 0" 
    unfolding mixed_H.P_nonterm_def using normHright normHcount 
    by (metis cmod_Re complex_of_real_nn_iff mixed_H.\<rho>count_pos mixed_H.\<rho>right_pos norm_le_zero_iff 
        norm_pths(2) norm_tc_pos norm_zero of_real_0)
  show "\<bar>mixed_H.Pleft P - mixed_H.Pright Proj_3\<bar> \<le> 
    2 * sqrt ((d+1) * Re (mixed_H.Pfind E))"
    using mixed_o2h_nonterm_3(1) terminH by auto
  show "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_H.Pright Proj_3)\<bar> \<le> 
    sqrt ((d+1) * Re (mixed_H.Pfind E))"
    using mixed_o2h_nonterm_3(2) terminH by auto
qed


text \<open>Theorem 1, definition of Pright (4)\<close>

theorem mixed_o2h_nonterm_4:
  shows 
    "\<bar>mixed_H.Pleft P - mixed_G.Pright Proj_3\<bar> \<le>  
  2 * sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    and 
    "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_G.Pright Proj_3)\<bar> \<le> 
  sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
proof -
  have "\<bar>mixed_H.Pleft P - mixed_G.Pright Proj_3\<bar> = 
    \<bar>mixed_H.Pleft' Proj_3 - mixed_H.Pright Proj_3\<bar>"
    using Pright_G_H_same unfolding mixed_G.Pleft_Pleft'_empty mixed_H.Pleft_Pleft'_empty
      Proj_3_def by auto
  also have "\<dots> \<le>  2 * sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    using mixed_H.estimate_Pfind[OF norm_Proj_3]
    by auto
  finally show "\<bar>mixed_H.Pleft P - mixed_G.Pright Proj_3\<bar> \<le>  
     2 * sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    by auto
  have "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_G.Pright Proj_3)\<bar> = 
    \<bar>sqrt (mixed_H.Pleft' Proj_3) - sqrt (mixed_H.Pright Proj_3)\<bar>"
    using Pright_G_H_same unfolding mixed_G.Pleft_Pleft'_empty mixed_H.Pleft_Pleft'_empty
      Proj_3_def by auto
  also have "\<dots> \<le> sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    using mixed_H.estimate_Pfind_sqrt[OF norm_Proj_3] by auto
  finally show "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_G.Pright Proj_3)\<bar> \<le> 
    sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    by auto
qed

theorem mixed_o2h_term_4:
  assumes "\<And>i. i<d+1 \<Longrightarrow> km_trace_preserving (kf_apply (E i))"
  shows 
    "\<bar>mixed_H.Pleft P - mixed_G.Pright Proj_3\<bar> \<le> 
  2 * sqrt ((d+1) * Re (mixed_H.Pfind E))"
    and 
    "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_G.Pright Proj_3)\<bar> \<le> 
  sqrt ((d+1) * Re (mixed_H.Pfind E))"
proof -
  have normHright: "norm (mixed_H.\<rho>right E) = 1" 
    by (rule mixed_H.trace_preserving_norm_\<rho>right[OF trace_preserving_kf_Fst[OF assms]])
  have normHcount: "norm (mixed_H.\<rho>count E) = 1" 
    by (rule mixed_H.trace_preserving_norm_\<rho>count[OF trace_preserving_kf_Fst[OF assms]])
  have terminH: "mixed_H.P_nonterm E = 0" 
    unfolding mixed_H.P_nonterm_def using normHright normHcount 
    by (metis cmod_Re complex_of_real_nn_iff mixed_H.\<rho>count_pos mixed_H.\<rho>right_pos norm_le_zero_iff 
        norm_pths(2) norm_tc_pos norm_zero of_real_0)
  show"\<bar>mixed_H.Pleft P - mixed_G.Pright Proj_3\<bar> \<le> 
    2 * sqrt ((d+1) * Re (mixed_H.Pfind E))"
    using mixed_o2h_nonterm_4(1) terminH by auto
  show "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_G.Pright Proj_3)\<bar> \<le> 
    sqrt ((d+1) * Re (mixed_H.Pfind E))"
    using mixed_o2h_nonterm_4(2) terminH by auto
qed


text \<open>Theorem 1: the definition of Pright (5) is
\<open>Pright = P[find \<or> b=1 for b<- A^{H\S}] = P(find for b<- A^{H\S}) + P(\<not> find \<and> b=1 for b<- A^{H\S})\<close>

Careful: In general, we cannot state quantum events with and or or. However, in the case that the 
two projectors commute, we may say
\<open>Pr(A \<and> B) \<equiv> PM_A o PM_B\<close>
\<open>Pr(A \<or> B) \<equiv> PM_A + PM_B - PM_A o PM_B\<close>

Still, for the projection, we need to joint the two projective spaces.
\<close>


definition Proj_5 :: "('mem \<times> 'l) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('mem \<times> 'l) ell2" where
  "Proj_5 = Proj (((P \<otimes>\<^sub>o id_cblinfun) *\<^sub>S \<top>) \<squnion> ((id_cblinfun \<otimes>\<^sub>o (id_cblinfun - selfbutter (ket empty))) *\<^sub>S \<top>))"

lemma is_Proj_5:
  "is_Proj Proj_5"
  unfolding Proj_5_def by (simp)


lemma Proj_5_altdef:
  "Proj_5 = Proj_3 + mixed_H.end_measure"
  unfolding Proj_5_def Proj_3_def by (subst splitting_Proj_or[OF mixed_H.is_Proj_P]) 
    (auto simp add: mixed_G.end_measure_def Snd_def butterfly_is_Proj)


lemma norm_Proj_5:
  "norm Proj_5 \<le> 1"
  unfolding Proj_5_def by (simp add: norm_is_Proj)




theorem mixed_o2h_nonterm_5:
  shows 
    "\<bar>mixed_H.Pleft P - (mixed_H.Pright Proj_5)\<bar> \<le>  
  2 * sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    and 
    "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_H.Pright Proj_5)\<bar> \<le> 
  sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
proof -
  have "\<bar>mixed_H.Pleft P - mixed_H.Pright Proj_5\<bar> = 
    \<bar>mixed_H.Pleft' Proj_5 - mixed_H.Pright Proj_5\<bar>"
    unfolding Proj_5_altdef Proj_3_def mixed_H.Pleft_Pleft'_case5[OF mixed_H.is_Proj_P] 
      mixed_H.Pfind_Pright Fst_def by auto
  also have "\<dots> \<le>  2 * sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    using mixed_H.estimate_Pfind[OF norm_Proj_5] by auto
  finally show "\<bar>mixed_H.Pleft P - mixed_H.Pright Proj_5\<bar> \<le>  
    2 * sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    by auto
  have "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_H.Pright Proj_5)\<bar> = 
    \<bar>sqrt (mixed_H.Pleft' Proj_5) - sqrt (mixed_H.Pright Proj_5)\<bar>"
    unfolding mixed_H.Pleft_Pleft'_case5[OF mixed_H.is_Proj_P] Proj_5_altdef Proj_3_def by auto
  also have "\<dots> \<le> sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    using mixed_H.estimate_Pfind_sqrt[OF norm_Proj_5] by auto
  finally show "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_H.Pright Proj_5)\<bar> \<le> 
    sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    by auto
qed

theorem mixed_o2h_term_5:
  assumes "\<And>i. i<d+1 \<Longrightarrow> km_trace_preserving (kf_apply (E i))"
  shows 
    "\<bar>mixed_H.Pleft P - mixed_H.Pright Proj_5\<bar> \<le> 
  2 * sqrt ((d+1) * Re (mixed_H.Pfind E))"
    and 
    "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_H.Pright Proj_5)\<bar> \<le> 
  sqrt ((d+1) * Re (mixed_H.Pfind E))"
proof -
  have normHright: "norm (mixed_H.\<rho>right E) = 1" 
    by (rule mixed_H.trace_preserving_norm_\<rho>right[OF trace_preserving_kf_Fst[OF assms]])
  have normHcount: "norm (mixed_H.\<rho>count E) = 1" 
    by (rule mixed_H.trace_preserving_norm_\<rho>count[OF trace_preserving_kf_Fst[OF assms]])
  have terminH: "mixed_H.P_nonterm E = 0" 
    unfolding mixed_H.P_nonterm_def using normHright normHcount 
    by (metis cmod_Re complex_of_real_nn_iff mixed_H.\<rho>count_pos mixed_H.\<rho>right_pos norm_le_zero_iff 
        norm_pths(2) norm_tc_pos norm_zero of_real_0)
  show "\<bar>mixed_H.Pleft P - mixed_H.Pright Proj_5\<bar> \<le> 
    2 * sqrt ((d+1) * Re (mixed_H.Pfind E))"
    using mixed_o2h_nonterm_5(1) terminH by auto
  show "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_H.Pright Proj_5)\<bar> \<le> 
    sqrt ((d+1) * Re (mixed_H.Pfind E))"
    using mixed_o2h_nonterm_5(2) terminH by auto
qed



text \<open>Theorem 1, definition of Pright (6)\<close>

lemma Pright_G_H_case5_nonterm:
  "mixed_H.Pright Proj_5 - mixed_G.Pright Proj_5 = norm (mixed_H.\<rho>right E) - norm (mixed_G.\<rho>right E)"
proof -
  have "mixed_H.Pright Proj_5 - mixed_G.Pright Proj_5 = 
    Re (trace_tc (compose_tcr Proj_5 (mixed_H.\<rho>right E))) -
    Re (trace_tc (compose_tcr Proj_5 (mixed_G.\<rho>right E)))"
    unfolding mixed_H.Pright_def mixed_G.Pright_def mixed_H.PM_altdef mixed_G.PM_altdef
    by (smt (verit, best) cblinfun_assoc_left(1) circularity_of_trace compose_tcr.rep_eq 
        from_trace_class_sandwich_tc is_Proj_5 is_Proj_algebraic sandwich_apply trace_class_from_trace_class 
        trace_tc.rep_eq)
  also have "\<dots> = Re (trace_tc (compose_tcr Proj_3 (mixed_H.\<rho>right E))) +
           Re (trace_tc (compose_tcr mixed_G.end_measure (mixed_H.\<rho>right E))) -
    Re (trace_tc (compose_tcr Proj_3 (mixed_G.\<rho>right E))) -
    Re (trace_tc (compose_tcr mixed_G.end_measure (mixed_G.\<rho>right E)))" 
    unfolding Proj_5_altdef by (auto simp add: compose_tcr.add_left trace_tc_plus)
  also have "\<dots> = Re (trace_tc (sandwich_tc (P \<otimes>\<^sub>o selfbutter (ket empty)) (mixed_H.\<rho>right E))) +
           Re (trace_tc (compose_tcr mixed_G.end_measure (mixed_H.\<rho>right E))) -
    Re (trace_tc (sandwich_tc (P \<otimes>\<^sub>o selfbutter (ket empty)) (mixed_G.\<rho>right E))) -
    Re (trace_tc (compose_tcr mixed_G.end_measure (mixed_G.\<rho>right E)))" 
    by (smt (verit, del_insts) Proj_3_def cblinfun_assoc_left(1) circularity_of_trace compose_tcr.rep_eq 
        from_trace_class_sandwich_tc is_Proj_3 is_Proj_algebraic sandwich_apply trace_class_from_trace_class 
        trace_tc.rep_eq)
  also have "\<dots> = mixed_H.Pright Proj_3 - mixed_G.Pright Proj_3 + Re (mixed_H.Pfind E - mixed_G.Pfind E)"
    by (simp add: Pright_G_H_same Proj_3_def \<rho>right_G_H_same mixed_G.Pfind_def mixed_H.Pfind_def)
  also have "\<dots> = Re (norm (mixed_H.\<rho>right E) - norm (mixed_G.\<rho>right E))"
    unfolding Proj_3_def by (simp add: Pfind_G_H_same_nonterm Pright_G_H_same)
  finally show ?thesis by auto
qed


lemma Pright_G_H_case5:
  assumes "\<And>i. i<d+1 \<Longrightarrow> km_trace_preserving (kf_apply (E i))"
  shows "mixed_H.Pright Proj_5 = mixed_G.Pright Proj_5"
proof -
  have normHright: "norm (mixed_H.\<rho>right E) = 1" 
    by (rule mixed_H.trace_preserving_norm_\<rho>right[OF trace_preserving_kf_Fst[OF assms]])
  moreover have normGright: "norm (mixed_G.\<rho>right E) = 1" 
    by (rule mixed_G.trace_preserving_norm_\<rho>right[OF trace_preserving_kf_Fst[OF assms]])
  ultimately show ?thesis using Pright_G_H_case5_nonterm by auto
qed


theorem mixed_o2h_nonterm_6:
  shows 
    "\<bar>mixed_H.Pleft P - mixed_G.Pright Proj_5\<bar> \<le>  
  2 * sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E) + 
    \<bar>norm (mixed_H.\<rho>right E) - norm (mixed_G.\<rho>right E)\<bar>"
    (* We leave out this version, because we get into trouble with the sqrt and the nontermination part.
and 
"\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_G.Pright Proj_5)\<bar> \<le> 
  sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E) + 
    \<bar>norm (mixed_H.\<rho>right E) - norm (mixed_G.\<rho>right E)\<bar>"
*)
proof -
  have "\<bar>mixed_H.Pleft P - mixed_G.Pright Proj_5\<bar> = 
    \<bar>mixed_H.Pleft P - mixed_H.Pright Proj_5 + norm (mixed_H.\<rho>right E) - norm (mixed_G.\<rho>right E)\<bar>"
    using Pright_G_H_case5_nonterm by auto
  also have "\<dots> \<le> \<bar>mixed_H.Pleft' Proj_5 - mixed_H.Pright Proj_5\<bar> + 
    \<bar>norm (mixed_H.\<rho>right E) - norm (mixed_G.\<rho>right E)\<bar>"
    using Proj_3_def Proj_5_altdef mixed_G.is_Proj_P mixed_H.Pleft_Pleft'_case5 by force
  also have "\<dots> \<le>  2 * sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E) + 
    \<bar>norm (mixed_H.\<rho>right E) - norm (mixed_G.\<rho>right E)\<bar>"
    using mixed_H.estimate_Pfind[OF norm_Proj_5] by auto
  finally show "\<bar>mixed_H.Pleft P - mixed_G.Pright Proj_5\<bar> \<le>  
     2 * sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E) + 
    \<bar>norm (mixed_H.\<rho>right E) - norm (mixed_G.\<rho>right E)\<bar>"
    by auto
qed


theorem mixed_o2h_term_6:
  assumes "\<And>i. i<d+1 \<Longrightarrow> km_trace_preserving (kf_apply (E i))"
  shows 
    "\<bar>mixed_H.Pleft P - mixed_G.Pright Proj_5\<bar> \<le> 
  2 * sqrt ((d+1) * Re (mixed_H.Pfind E))"
    and 
    "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_G.Pright Proj_5)\<bar> \<le> 
  sqrt ((d+1) * Re (mixed_H.Pfind E))"
proof -
  have normHright: "norm (mixed_H.\<rho>right E) = 1" 
    by (rule mixed_H.trace_preserving_norm_\<rho>right[OF trace_preserving_kf_Fst[OF assms]])
  have normGright: "norm (mixed_G.\<rho>right E) = 1" 
    by (rule mixed_G.trace_preserving_norm_\<rho>right[OF trace_preserving_kf_Fst[OF assms]])
  have normHcount: "norm (mixed_H.\<rho>count E) = 1" 
    by (rule mixed_H.trace_preserving_norm_\<rho>count[OF trace_preserving_kf_Fst[OF assms]])
  have terminH: "mixed_H.P_nonterm E = 0" 
    unfolding mixed_H.P_nonterm_def using normHright normHcount 
    by (metis cmod_Re complex_of_real_nn_iff mixed_H.\<rho>count_pos mixed_H.\<rho>right_pos norm_le_zero_iff 
        norm_pths(2) norm_tc_pos norm_zero of_real_0)
  show"\<bar>mixed_H.Pleft P - mixed_G.Pright Proj_5\<bar> \<le> 
    2 * sqrt ((d+1) * Re (mixed_H.Pfind E))"
    using mixed_o2h_nonterm_6(1) terminH unfolding normHright normGright by auto

  have nonterm_zero: "mixed_H.P_nonterm E = 0"
    unfolding mixed_H.P_nonterm_def using normHright normHcount
      mixed_H.P_nonterm_def terminH by presburger
  have "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_G.Pright Proj_5)\<bar> = 
    \<bar>sqrt (mixed_H.Pleft' Proj_5) - sqrt (mixed_H.Pright Proj_5)\<bar>"
    using Pright_G_H_case5[OF assms, symmetric] 
    unfolding mixed_H.Pleft_Pleft'_case5[OF mixed_H.is_Proj_P]
      Proj_5_altdef Proj_3_def by auto
  also have "\<dots> \<le> sqrt ((d+1) * Re (mixed_H.Pfind E) + d* mixed_H.P_nonterm E)"
    using mixed_H.estimate_Pfind_sqrt[OF norm_Proj_5] by auto
  finally show "\<bar>sqrt (mixed_H.Pleft P) - sqrt (mixed_G.Pright Proj_5)\<bar> \<le> 
    sqrt ((d+1) * Re (mixed_H.Pfind E))"
    using nonterm_zero by auto
qed



end

unbundle no cblinfun_syntax
unbundle no lattice_syntax
unbundle no register_syntax


end