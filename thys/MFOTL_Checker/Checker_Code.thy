(*<*)
theory Checker_Code
  imports 
    Checker Event_Data 
    "HOL-Library.Code_Target_Nat" 
    "HOL.String"
    "HOL-Library.List_Lexorder" 
    "HOL-Library.AList_Mapping"
    "HOL-Library.Cardinality"
begin
(*>*)

section \<open>Code Generation\<close>

subsection \<open>Type Class Instances\<close>

class universe =
  fixes universe :: "'a list option"
  assumes infinite: "universe = None \<Longrightarrow> infinite (UNIV :: 'a set)"
  and finite: "universe = Some xs \<Longrightarrow> distinct xs \<and> set xs = UNIV"
begin

lemma finite_coset: "finite (List.coset (xs :: 'a list)) = (case universe of None \<Rightarrow> False | _ \<Rightarrow> True)"
  using infinite finite
  by (auto split: option.splits dest!: equalityD2 elim!: finite_subset)

end

declare [[code drop: finite]]
declare finite_set[THEN eqTrueI, code] finite_coset[code]

instantiation bool :: universe begin
definition universe_bool :: "bool list option" where "universe_bool = Some [True, False]"
instance by standard (auto simp: universe_bool_def)
end
instantiation char :: universe begin
definition universe_char :: "char list option" where "universe_char = Some (map char_of [0::nat..<256])"
instance by standard (use UNIV_char_of_nat in \<open>auto simp: universe_char_def distinct_map\<close>)
end
instantiation nat :: universe begin
definition universe_nat :: "nat list option" where "universe_nat = None"
instance by standard (auto simp: universe_nat_def)
end
instantiation list :: (type) universe begin
definition universe_list :: "'a list list option" where "universe_list = None"
instance by standard (auto simp: universe_list_def infinite_UNIV_listI)
end
instantiation String.literal :: universe begin
definition universe_literal :: "String.literal list option" where "universe_literal = None"
instance by standard (auto simp: universe_literal_def infinite_literal)
end
instantiation string8 :: universe begin
definition universe_string8 :: "string8 list option" where "universe_string8 = None"
lemma UNIV_string8: "UNIV = Abs_string8 ` UNIV"
  by (auto simp: image_iff intro: Abs_string8_cases)
instance by standard
  (auto simp: universe_string8_def UNIV_string8 finite_image_iff Abs_string8_inject inj_on_def infinite_UNIV_listI)
end
instantiation prod :: (universe, universe) universe begin
definition universe_prod :: "('a \<times> 'b) list option" where "universe_prod =
  (case (universe, universe) of (Some xs, Some ys) \<Rightarrow> Some (List.product xs ys) | _ \<Rightarrow> None)"
instance by standard
  (auto simp: universe_prod_def finite_prod distinct_product infinite finite split: option.splits)
end
instantiation sum :: (universe, universe) universe begin
definition universe_sum :: "('a + 'b) list option" where "universe_sum =
  (case (universe, universe) of (Some xs, Some ys) \<Rightarrow> Some (map Inl xs @ map Inr ys) | _ \<Rightarrow> None)"
instance by standard
  (use UNIV_sum in \<open>auto simp: universe_sum_def distinct_map infinite finite split: option.splits\<close>)
end
instantiation option :: (universe) universe begin
definition "universe_option = (case universe of Some xs \<Rightarrow> Some (None # map Some xs) | _ \<Rightarrow> None)"
instance by standard (auto simp: universe_option_def distinct_map finite infinite image_iff split: option.splits)
end
instantiation "fun" :: (universe, universe) universe begin
definition universe_fun :: "('a \<Rightarrow> 'b) list option" where "universe_fun = 
  (case (universe, universe) of
    (Some xs, Some ys) \<Rightarrow> Some (map (\<lambda>zs. the \<circ> map_of (zip xs zs)) (List.n_lists (length xs) ys))
  | (_, Some [x]) \<Rightarrow> Some [\<lambda>_. x]
  | _ \<Rightarrow> None)"
instance
proof -
  have 1: False if "infinite (UNIV::'a set)" "CARD('b) = Suc 0" "a \<noteq> b" for a b :: 'b
    using that by (metis (full_types) UNIV_I card_1_singleton_iff singletonD)
  have 2: "ys = zs"
    if "distinct (xs::'a list)" and "length ys = length xs" and "length zs = length xs"
    and "\<forall>a. the (map_of (zip xs ys) a) = the (map_of (zip xs zs) a)"
    for xs :: "'a list" and ys zs :: "'b list"
    using that by (metis map_fst_zip map_of_eqI map_of_zip_inject map_of_zip_is_None option.expand)
  have 3: "\<exists>zs. length zs = length xs \<and> set zs \<subseteq> set ys \<and> (\<forall>x. f x = the (map_of (zip xs zs) x))"
    if "\<forall>x. x \<in> set xs" "\<forall>x. x \<in> set ys"
    for xs ys and f :: "'a \<Rightarrow> 'b"
    using that by (metis length_map map_of_zip_map option.sel subsetI)
  show "OFCLASS('a \<Rightarrow> 'b, universe_class)"
    by standard
      (auto 0 3 simp: universe_fun_def set_eq_iff fun_eq_iff image_iff set_n_lists distinct_map
        inj_on_def distinct_n_lists finite_UNIV_fun dest!: infinite finite
        split: option.splits list.splits intro: 1 2 3)
qed
end
instantiation event_data :: universe begin
definition universe_event_data :: "event_data list option" where "universe_event_data = None"  
instance by standard (simp_all add: infinite_UNIV_event_data universe_event_data_def)
end

instantiation nat :: default begin
definition default_nat :: nat where "default_nat = 0"
instance proof qed
end

instantiation list :: (type) default begin
definition default_list :: "'a list" where "default_list = []"
instance proof qed
end

instance event_data :: equal by standard

instantiation String.literal :: default begin
definition default_literal :: String.literal where "default_literal = 0"
instance proof qed
end

instantiation event_data :: card_UNIV begin
definition "finite_UNIV = Phantom(event_data) False"
definition "card_UNIV = Phantom(event_data) 0"
instance by intro_classes (simp_all add: finite_UNIV_event_data_def card_UNIV_event_data_def infinite_UNIV_event_data)
end

subsection \<open>Progress\<close>

primrec progress :: "('n, 'd) trace \<Rightarrow> ('n, 'd) Formula.formula \<Rightarrow> nat \<Rightarrow> nat" where
  "progress \<sigma> Formula.TT j = j"
| "progress \<sigma> Formula.FF j = j"
| "progress \<sigma> (Formula.Eq_Const _ _) j = j"
| "progress \<sigma> (Formula.Pred _ _) j = j"
| "progress \<sigma> (Formula.Neg \<phi>) j = progress \<sigma> \<phi> j"
| "progress \<sigma> (Formula.Or \<phi> \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
| "progress \<sigma> (Formula.And \<phi> \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
| "progress \<sigma> (Formula.Imp \<phi> \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
| "progress \<sigma> (Formula.Iff \<phi> \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
| "progress \<sigma> (Formula.Exists _ \<phi>) j = progress \<sigma> \<phi> j"
| "progress \<sigma> (Formula.Forall _ \<phi>) j = progress \<sigma> \<phi> j"
| "progress \<sigma> (Formula.Prev I \<phi>) j = (if j = 0 then 0 else min (Suc (progress \<sigma> \<phi> j)) j)"
| "progress \<sigma> (Formula.Next I \<phi>) j = progress \<sigma> \<phi> j - 1"
| "progress \<sigma> (Formula.Once I \<phi>) j = progress \<sigma> \<phi> j"
| "progress \<sigma> (Formula.Historically I \<phi>) j = progress \<sigma> \<phi> j"
| "progress \<sigma> (Formula.Eventually I \<phi>) j =
    Inf {i. \<forall>k. k < j \<and> k \<le> (progress \<sigma> \<phi> j) \<longrightarrow> (\<tau> \<sigma> k - \<tau> \<sigma> i) \<le> right I}"
| "progress \<sigma> (Formula.Always I \<phi>) j =
    Inf {i. \<forall>k. k < j \<and> k \<le> (progress \<sigma> \<phi> j) \<longrightarrow> (\<tau> \<sigma> k - \<tau> \<sigma> i) \<le> right I}"
| "progress \<sigma> (Formula.Since \<phi> I \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
| "progress \<sigma> (Formula.Until \<phi> I \<psi>) j =
    Inf {i. \<forall>k. k < j \<and> k \<le> min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j) \<longrightarrow> (\<tau> \<sigma> k - \<tau> \<sigma> i) \<le> right I}"

lemma Inf_Min:
  fixes P :: "nat \<Rightarrow> bool"
  assumes "P j"
  shows "Inf (Collect P) = Min (Set.filter P {..j})"
  using Min_in[where ?A="Set.filter P {..j}"] assms
  by (auto simp: Set.filter_def intro: cInf_lower intro!: antisym[OF _ Min_le])
    (metis Inf_nat_def1 empty_iff mem_Collect_eq)

lemma progress_Eventually_code: "progress \<sigma> (Formula.Eventually I \<phi>) j =
  (let m = min j (Suc (progress \<sigma> \<phi> j)) - 1 in Min (Set.filter (\<lambda>i. enat (\<delta> \<sigma> m i) \<le> right I) {..j}))"
proof -
  define P where "P \<equiv> (\<lambda>i. \<forall>k. k < j \<and> k \<le> (progress \<sigma> \<phi> j) \<longrightarrow> enat (\<delta> \<sigma> k i) \<le> right I)"
  have P_j: "P j"
    by (auto simp: P_def enat_0)
  have all_wit: "(\<forall>k \<in> {..<m}. enat (\<delta> \<sigma> k i) \<le> right I) \<longleftrightarrow> (enat (\<delta> \<sigma> (m - 1) i) \<le> right I)" for i m
  proof (cases m)
    case (Suc ma)
    have "k < Suc ma \<Longrightarrow> \<delta> \<sigma> k i \<le> \<delta> \<sigma> ma i" for k
      using \<tau>_mono
      unfolding less_Suc_eq_le
      by (rule diff_le_mono)
    then show ?thesis
      by (auto simp: Suc) (meson order.trans enat_ord_simps(1))
  qed (auto simp: enat_0)
  show ?thesis
    unfolding progress.simps Let_def P_def[symmetric] Inf_Min[where ?P=P, OF P_j] all_wit[symmetric]
    by (fastforce simp: P_def intro: arg_cong[where ?f=Min])
qed

lemma progress_Always_code: "progress \<sigma> (Formula.Always I \<phi>) j =
  (let m = min j (Suc (progress \<sigma> \<phi> j)) - 1 in Min (Set.filter (\<lambda>i. enat (\<delta> \<sigma> m i) \<le> right I) {..j}))"
proof -
  define P where "P \<equiv> (\<lambda>i. \<forall>k. k < j \<and> k \<le> (progress \<sigma> \<phi> j) \<longrightarrow> enat (\<delta> \<sigma> k i) \<le> right I)"
  have P_j: "P j"
    by (auto simp: P_def enat_0)
  have all_wit: "(\<forall>k \<in> {..<m}. enat (\<delta> \<sigma> k i) \<le> right I) \<longleftrightarrow> (enat (\<delta> \<sigma> (m - 1) i) \<le> right I)" for i m
  proof (cases m)
    case (Suc ma)
    have "k < Suc ma \<Longrightarrow> \<delta> \<sigma> k i \<le> \<delta> \<sigma> ma i" for k
      using \<tau>_mono
      unfolding less_Suc_eq_le
      by (rule diff_le_mono)
    then show ?thesis
      by (auto simp: Suc) (meson order.trans enat_ord_simps(1))
  qed (auto simp: enat_0)
  show ?thesis
    unfolding progress.simps Let_def P_def[symmetric] Inf_Min[where ?P=P, OF P_j] all_wit[symmetric]
    by (fastforce simp: P_def intro: arg_cong[where ?f=Min])
qed

lemma progress_Until_code: "progress \<sigma> (Formula.Until \<phi> I \<psi>) j =
  (let m = min j (Suc (min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j))) - 1 in Min (Set.filter (\<lambda>i. enat (\<delta> \<sigma> m i) \<le> right I) {..j}))"
proof -
  define P where "P \<equiv> (\<lambda>i. \<forall>k. k < j \<and> k \<le> min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j) \<longrightarrow> enat (\<delta> \<sigma> k i) \<le> right I)"
  have P_j: "P j"
    by (auto simp: P_def enat_0)
  have all_wit: "(\<forall>k \<in> {..<m}. enat (\<delta> \<sigma> k i) \<le> right I) \<longleftrightarrow> (enat (\<delta> \<sigma> (m - 1) i) \<le> right I)" for i m
  proof (cases m)
    case (Suc ma)
    have "k < Suc ma \<Longrightarrow> \<delta> \<sigma> k i \<le> \<delta> \<sigma> ma i" for k
      using \<tau>_mono
      unfolding less_Suc_eq_le
      by (rule diff_le_mono)
    then show ?thesis
      by (auto simp: Suc) (meson order.trans enat_ord_simps(1))
  qed (auto simp: enat_0)
  show ?thesis
    unfolding progress.simps Let_def P_def[symmetric] Inf_Min[where ?P=P, OF P_j] all_wit[symmetric]
    by (fastforce simp: P_def intro: arg_cong[where ?f=Min])
qed

lemmas progress_code[code] = progress.simps(1-15) progress_Eventually_code progress_Always_code progress.simps(18) progress_Until_code

subsection \<open>Trace\<close>

lemma snth_Stream_eq: "(x ## s) !! n = (case n of 0 \<Rightarrow> x | Suc m \<Rightarrow> s !! m)"
  by (cases n) auto

lemma extend_is_stream: 
  assumes "sorted (map snd list)"
  and "\<And>x. x \<in> set list \<Longrightarrow> snd x \<le> m"
  and "\<And>x. x \<in> set list \<Longrightarrow> finite (fst x)"
  shows "ssorted (smap snd (list @- smap (\<lambda>n. ({}, n + m)) nats)) \<and>
    sincreasing (smap snd (list @- smap (\<lambda>n. ({}, n + m)) nats)) \<and>
    sfinite (smap fst (list @- smap (\<lambda>n. ({}, n + m)) nats))"
proof -
  have A: "\<forall>x\<in>set list. n \<le> snd x \<Longrightarrow> n \<le> m \<Longrightarrow>
    n \<le> (map snd list @- smap (\<lambda>x. x + m) nats) !! i" for n i 
    and list :: "('a set \<times> nat) list"
  proof (induction i arbitrary: n)
    case (Suc i)
    then show ?case
      by (auto simp: shift_snth nth_tl)
  qed (auto simp add: list.map_sel(1))
  then have "ssorted (smap snd (list @- smap (\<lambda>n. ({}, n + m)) nats))"
    using assms
      by (induction list) (auto simp: stream.map_comp o_def ssorted_iff_mono snth_Stream_eq
        split: nat.splits)
  moreover have "sincreasing (smap snd (list @- smap (\<lambda>n. ({}, n + m)) nats))"
    using assms
  proof (induction list)
    case Nil
    then show ?case
      by (simp add: sincreasing_def) presburger
  next
    case (Cons a as)
    have IH: "\<And>x. \<exists>i. x < smap snd (as @- smap (\<lambda>n. ({}, n + m)) nats) !! i"
      using Cons
      by (simp add: sincreasing_def)
    show ?case
      using IH
      by (simp add: sincreasing_def) 
        (metis snth_Stream)
  qed
  moreover have "sfinite (smap fst (list @- smap (\<lambda>n. ({}, n + m)) nats))"
    using assms(3)
  proof (induction list)
    case Nil
    then show ?case by (simp add: sfinite_def)
  next
    case (Cons a as)
    then have fin: "finite (fst a)"
      by simp
    show ?case
      using Cons 
      by (auto simp add: sfinite_def snth_Stream_eq split: nat.splits)
  qed
  ultimately show ?thesis
    by simp
qed

typedef 'a trace_mapping = "{(n, m, t) :: (nat \<times> nat \<times> (nat, 'a set \<times> nat) mapping) |
  n m t. Mapping.keys t = {..<n} \<and>
  sorted (map (snd \<circ> (the \<circ> Mapping.lookup t)) [0..<n]) \<and>
  (case n of 0 \<Rightarrow> True | Suc n' \<Rightarrow> (case Mapping.lookup t n' of Some (X', t') \<Rightarrow> t' \<le> m | None \<Rightarrow> False)) \<and> 
  (\<forall>n' < n. case Mapping.lookup t n' of Some (X', t') \<Rightarrow> finite X' | None \<Rightarrow> False)}"
  by (rule exI[of _ "(0, 0, Mapping.empty)"]) auto

setup_lifting type_definition_trace_mapping

lemma lookup_bulkload_Some: "i < length list \<Longrightarrow>
  Mapping.lookup (Mapping.bulkload list) i = Some (list ! i)"
  by transfer auto

lift_definition trace_mapping_of_list :: "('a set \<times> nat) list \<Rightarrow> 'a trace_mapping" is
  "\<lambda>xs. if sorted (map snd xs) \<and> (\<forall>x \<in> set xs. finite (fst x)) then (if xs = [] then (0, 0, Mapping.empty)
  else (length xs, snd (last xs), Mapping.bulkload xs))
  else (0, 0, Mapping.empty)"
  by (auto simp: lookup_bulkload_Some sorted_iff_nth_Suc last_conv_nth
    list_all_iff in_set_conv_nth Ball_def Bex_def image_iff split: nat.splits)

lift_definition trace_mapping_nth :: "'a trace_mapping \<Rightarrow> nat \<Rightarrow> ('a set \<times> nat)" is
  "\<lambda>(n, m, t) i. if i < n then the (Mapping.lookup t i) else ({}, (i - n) + m)" .

lift_definition Trace_Mapping :: "'a trace_mapping \<Rightarrow> 'a Trace.trace" is
  "\<lambda>(n, m, t). map (the \<circ> Mapping.lookup t) [0..<n] @- smap (\<lambda>n. ({} :: 'a set, n + m)) nats"
proof (goal_cases)
  case (1 prod)
  obtain n m t where prod_def: "prod = (n, m, t)"
    by (cases prod) auto
  have props: "Mapping.keys t = {..<n}"
    "sorted (map (snd \<circ> (the \<circ> Mapping.lookup t)) [0..<n])"
    "(case n of 0 \<Rightarrow> True | Suc n' \<Rightarrow> (case Mapping.lookup t n' of Some (X', t') \<Rightarrow> t' \<le> m | None \<Rightarrow> False))"
    "(\<forall>n' < n. case Mapping.lookup t n' of Some (X', t') \<Rightarrow> finite X' | None \<Rightarrow> False)"
    using 1 by (auto simp add: prod_def)
  have aux: "x \<in> set (map (the \<circ> Mapping.lookup t) [0..<n]) \<Longrightarrow> snd x \<le> m" for x
    using props(2,3) less_Suc_eq_le
    by (fastforce simp: sorted_iff_nth_mono split: nat.splits option.splits)
  have aux2: "x \<in> set (map (the \<circ> Mapping.lookup t) [0..<n]) \<Longrightarrow> finite (fst x)" for x
    using props(1,4)
    by (auto split: nat.splits option.splits)
  show ?case
    unfolding prod_def prod.case
    by (rule extend_is_stream[where ?m=m]) (use props aux aux2 in \<open>auto simp: prod_def\<close>)
qed

code_datatype Trace_Mapping

definition "trace_of_list xs = Trace_Mapping (trace_mapping_of_list xs)"

lemma \<Gamma>_rbt_code[code]: "\<Gamma> (Trace_Mapping t) i = fst (trace_mapping_nth t i)"
  by transfer (auto split: prod.splits)

lemma \<tau>_rbt_code[code]: "\<tau> (Trace_Mapping t) i = snd (trace_mapping_nth t i)"
  by transfer (auto split: prod.splits)
                                       
lemma trace_mapping_of_list_sound: "sorted (map snd xs) \<and> (\<forall>x \<in> set xs. finite (fst x)) \<Longrightarrow> i < length xs \<Longrightarrow>
  xs ! i = (\<Gamma> (trace_of_list xs) i, \<tau> (trace_of_list xs) i)"
  unfolding trace_of_list_def
  by transfer (auto simp: lookup_bulkload_Some)

subsection \<open>Auxiliary results\<close>

definition "sum_proofs f xs = sum_list (map f xs)"

lemma sum_proofs_empty[simp]: "sum_proofs f [] = 0"
  by (auto simp: sum_proofs_def)

lemma sum_proofs_fundef_cong[fundef_cong]: "(\<And>x. x \<in> set xs \<Longrightarrow> f x = f' x) \<Longrightarrow>
  sum_proofs f xs = sum_proofs f' xs"
  by (induction xs) (auto simp: sum_proofs_def)

lemma sum_proofs_Cons:
  fixes f :: "'a \<Rightarrow> nat"
  shows "sum_proofs f (p # qs) = f p + sum_proofs f qs"
  by (auto simp: sum_proofs_def split: list.splits)

lemma sum_proofs_app:
  fixes f :: "'a \<Rightarrow> nat"
  shows "sum_proofs f (qs @ [p]) = f p + sum_proofs f qs"
  by (auto simp: sum_proofs_def split: list.splits)

context
  fixes w :: "'n \<Rightarrow> nat"
begin

function (sequential) s_pred :: "('n, 'd) sproof \<Rightarrow> nat" 
  and v_pred :: "('n, 'd) vproof \<Rightarrow> nat" where
  "s_pred (STT _) = 1"
| "s_pred (SEq_Const _ _ _) = 1"
| "s_pred (SPred _ r _) = w r"
| "s_pred (SNeg vp) = (v_pred vp) + 1"
| "s_pred (SOrL sp1) = (s_pred sp1) + 1"
| "s_pred (SOrR sp2) = (s_pred sp2) + 1"
| "s_pred (SAnd sp1 sp2) = (s_pred sp1) + (s_pred sp2) + 1"
| "s_pred (SImpL vp1) = (v_pred vp1) + 1"
| "s_pred (SImpR sp2) = (s_pred sp2) + 1"
| "s_pred (SIffSS sp1 sp2) = (s_pred sp1) + (s_pred sp2) + 1"
| "s_pred (SIffVV vp1 vp2) = (v_pred vp1) + (v_pred vp2) + 1"
| "s_pred (SExists _ _ sp) = (s_pred sp) + 1"
| "s_pred (SForall _ part) = (sum_proofs s_pred (vals part)) + 1"
| "s_pred (SPrev sp) = (s_pred sp) + 1"
| "s_pred (SNext sp) = (s_pred sp) + 1"
| "s_pred (SOnce _ sp) = (s_pred sp) + 1"
| "s_pred (SEventually _ sp) = (s_pred sp) + 1"
| "s_pred (SHistorically _ _ sps) = (sum_proofs s_pred sps) + 1"
| "s_pred (SHistoricallyOut _) = 1"
| "s_pred (SAlways _ _ sps) = (sum_proofs s_pred sps) + 1"
| "s_pred (SSince sp2 sp1s) = (sum_proofs s_pred (sp2 # sp1s)) + 1"
| "s_pred (SUntil sp1s sp2) = (sum_proofs s_pred (sp1s @ [sp2])) + 1"
| "v_pred (VFF _ ) = 1"
| "v_pred (VEq_Const _ _ _) = 1"
| "v_pred (VPred _ r _) = w r"
| "v_pred (VNeg sp) = (s_pred sp) + 1"
| "v_pred (VOr vp1 vp2) = ((v_pred vp1) + (v_pred vp2)) + 1"
| "v_pred (VAndL vp1) = (v_pred vp1) + 1"
| "v_pred (VAndR vp2) = (v_pred vp2) + 1"
| "v_pred (VImp sp1 vp2) = ((s_pred sp1) + (v_pred vp2)) + 1"
| "v_pred (VIffSV sp1 vp2) = ((s_pred sp1) + (v_pred vp2)) + 1"
| "v_pred (VIffVS vp1 sp2) = ((v_pred vp1) + (s_pred sp2)) + 1"
| "v_pred (VExists _ part) = (sum_proofs v_pred (vals part)) + 1"
| "v_pred (VForall _ _ vp) = (v_pred vp) + 1"
| "v_pred (VPrev vp) = (v_pred vp) + 1"
| "v_pred (VPrevZ) = 1"
| "v_pred (VPrevOutL _) = 1"
| "v_pred (VPrevOutR _) = 1"
| "v_pred (VNext vp) = (v_pred vp) + 1"
| "v_pred (VNextOutL _) = 1"
| "v_pred (VNextOutR _) = 1"
| "v_pred (VOnceOut _) = 1"
| "v_pred (VOnce _ _ vps) = (sum_proofs v_pred vps) + 1"
| "v_pred (VEventually _ _ vps) = (sum_proofs v_pred vps) + 1"
| "v_pred (VHistorically _ vp) = (v_pred vp) + 1"
| "v_pred (VAlways _ vp) = (v_pred vp) + 1"
| "v_pred (VSinceOut _) = 1"
| "v_pred (VSince _ vp1 vp2s) = (sum_proofs v_pred (vp1 # vp2s)) + 1"
| "v_pred (VSinceInf _ _ vp2s) = (sum_proofs v_pred vp2s) + 1"
| "v_pred (VUntil _ vp2s vp1) = (sum_proofs v_pred (vp2s @ [vp1])) + 1"
| "v_pred (VUntilInf _ _ vp2s) = (sum_proofs v_pred vp2s) + 1"
  by pat_completeness auto
termination
  by (relation "measure (case_sum size size)")
    (auto simp add: termination_simp)

definition p_pred :: "('n, 'd) proof \<Rightarrow> nat" where
  "p_pred = case_sum s_pred v_pred"

end

subsection \<open>\<^const>\<open>v_check_exec\<close> setup\<close>

lemma ETP_minus_le_iff: "ETP \<sigma> (\<tau> \<sigma> i - n) \<le> j \<longleftrightarrow> \<delta> \<sigma> i j \<le> n"
  by (simp add: add.commute i_ETP_tau le_diff_conv)

lemma ETP_minus_gt_iff: "j < ETP \<sigma> (\<tau> \<sigma> i - n) \<longleftrightarrow> \<delta> \<sigma> i j > n"
  by (meson ETP_minus_le_iff leD le_less_linear)

lemma nat_le_iff_less:
  fixes n :: nat
  shows "(j \<le> n) \<longleftrightarrow> (j = 0 \<or> j - 1 < n)"
  by auto

lemma ETP_minus_eq_iff: "j = ETP \<sigma> (\<tau> \<sigma> i - n) \<longleftrightarrow> ((j = 0 \<or> n < \<delta> \<sigma> i (j - 1)) \<and> \<delta> \<sigma> i j \<le> n)"
  unfolding eq_iff[of j "ETP \<sigma> (\<tau> \<sigma> i - n)"] nat_le_iff_less[of j] ETP_minus_le_iff ETP_minus_gt_iff
  by auto

lemma LTP_minus_ge_iff: "\<tau> \<sigma> 0 + n \<le> \<tau> \<sigma> i \<Longrightarrow> j \<le> LTP \<sigma> (\<tau> \<sigma> i - n) \<longleftrightarrow>
  (case n of 0 \<Rightarrow> \<delta> \<sigma> j i = 0 | _ \<Rightarrow> j \<le> i \<and> \<delta> \<sigma> i j \<ge> n)"
  using \<tau>_mono[of i j \<sigma>]
  by (fastforce simp add: i_LTP_tau le_diff_conv2 Suc_le_eq split: nat.splits)

lemma LTP_plus_ge_iff: "j \<le> LTP \<sigma> (\<tau> \<sigma> i + n) \<longleftrightarrow> \<delta> \<sigma> j i \<le> n"
  by (simp add: add.commute i_LTP_tau le_diff_conv trans_le_add2)

lemma LTP_minus_lt_if:
  assumes "j \<le> i" "\<tau> \<sigma> 0 + n \<le> \<tau> \<sigma> i" "\<delta> \<sigma> i j < n"
  shows "LTP \<sigma> (\<tau> \<sigma> i - n) < j"
proof -
  have not_in: "k \<notin> {ia. \<tau> \<sigma> ia \<le> \<tau> \<sigma> i - n}" if "j \<le> k" for k
    using assms \<tau>_mono[OF that, of \<sigma>]
    by auto
  then have "{ia. \<tau> \<sigma> ia \<le> \<tau> \<sigma> i - n} \<subseteq> {0..<j}"
    using not_le_imp_less
    by (clarsimp; blast)
  then have "finite {ia. \<tau> \<sigma> ia \<le> \<tau> \<sigma> i - n}"
    using subset_eq_atLeast0_lessThan_finite
    by blast
  moreover have "0 \<in> {ia. \<tau> \<sigma> ia \<le> \<tau> \<sigma> i - n}"
    using assms(2)
    by auto
  ultimately show ?thesis
    unfolding LTP_def
    by (metis Max_in not_in empty_iff not_le_imp_less)
qed

lemma LTP_minus_lt_iff:
  assumes "\<tau> \<sigma> 0 + n \<le> \<tau> \<sigma> i"
  shows "LTP \<sigma> (\<tau> \<sigma> i - n) < j \<longleftrightarrow> (if \<not> j \<le> i \<and> n = 0 then \<delta> \<sigma> j i > 0 else \<delta> \<sigma> i j < n)"
proof (cases "j \<le> i")
  case True
  then show ?thesis
    using assms i_le_LTPi_minus[of \<sigma> n i] LTP_minus_lt_if[of j i \<sigma> n]
    by (cases n)
      (auto simp add: i_LTP_tau linorder_not_less Suc_le_eq dest!: tau_LTP_k[rotated])
next
  case False
  have delta: "\<delta> \<sigma> i j = 0"
    using False
    by auto
  show ?thesis
  proof (cases n)
    case 0
    then show ?thesis
      using False assms
      by (metis add.right_neutral diff_is_0_eq diff_zero i_LTP_tau linorder_not_less)
  next
    case (Suc n')
    then show ?thesis
      using False assms
      by (cases i)
        (auto simp: Suc_le_eq not_le elim!: order.strict_trans[rotated] intro!: i_le_LTPi_minus)
  qed
qed

lemma LTP_minus_eq_iff:
  assumes "\<tau> \<sigma> 0 + n \<le> \<tau> \<sigma> i"
  shows "j = LTP \<sigma> (\<tau> \<sigma> i - n) \<longleftrightarrow>
  (case n of 0 \<Rightarrow> i \<le> j \<and> \<delta> \<sigma> j i = 0 \<and> \<delta> \<sigma> (Suc j) j > 0
  | _ \<Rightarrow> j \<le> i \<and> n \<le> \<delta> \<sigma> i j \<and> \<delta> \<sigma> i (Suc j) < n)"
proof (cases n)
  case 0
  show ?thesis
    using assms 0 i_LTP_tau[of \<sigma> "\<tau> \<sigma> i" "LTP \<sigma> (\<tau> \<sigma> i)"]
      i_LTP_tau[of \<sigma> "\<tau> \<sigma> i" "Suc (LTP \<sigma> (\<tau> \<sigma> i))"] i_LTP_tau[of \<sigma> "\<tau> \<sigma> i" "j"]
      less_\<tau>D[of \<sigma> "(LTP \<sigma> (\<tau> \<sigma> i))" "Suc j"]
    by (auto simp: i_le_LTPi not_le elim!: antisym dest!:
      order_antisym_conv[of "\<tau> \<sigma> i" "\<tau> \<sigma> j", THEN iffD1, rotated]
      order_antisym_conv[of "\<tau> \<sigma> i" "\<tau> \<sigma> (LTP \<sigma> (\<tau> \<sigma> i))", THEN iffD1, rotated])
next
  case (Suc n')
  show ?thesis
    using assms
    by (simp add: Suc eq_iff[of j "LTP \<sigma> (\<tau> \<sigma> i - Suc n')"] less_Suc_eq_le[of "LTP \<sigma> (\<tau> \<sigma> i - Suc n')" j, symmetric] LTP_minus_ge_iff LTP_minus_lt_iff)
qed

lemma LTP_plus_eq_iff:
  shows "j = LTP \<sigma> (\<tau> \<sigma> i + n) \<longleftrightarrow> (\<delta> \<sigma> j i \<le> n \<and> \<delta> \<sigma> (Suc j) i > n)"
  unfolding eq_iff[of j "LTP \<sigma> (\<tau> \<sigma> i + n)"]
  by (meson LTP_plus_ge_iff linorder_not_less not_less_eq_eq)

lemma LTP_p_def: "\<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i \<Longrightarrow> LTP_p \<sigma> i I = (case left I of 0 \<Rightarrow> i | _ \<Rightarrow> LTP \<sigma> (\<tau> \<sigma> i - left I))"
  using i_le_LTPi by (auto simp: min_def i_LTP_tau split: nat.splits)

definition "check_upt_LTP_p \<sigma> I li xs i \<longleftrightarrow> (case xs of [] \<Rightarrow>
  (case left I of 0 \<Rightarrow> i < li | Suc n \<Rightarrow>
    (if \<not> li \<le> i \<and> left I = 0 then 0 < \<delta> \<sigma> li i else \<delta> \<sigma> i li < left I))
  | _ \<Rightarrow> xs = [li..<li + length xs] \<and>
    (case left I of 0 \<Rightarrow> li + length xs - 1 = i | Suc n \<Rightarrow>
      (li + length xs - 1 \<le> i \<and> left I \<le> \<delta> \<sigma> i (li + length xs - 1) \<and> \<delta> \<sigma> i (li + length xs) < left I)))"

lemma check_upt_l_cong:
  assumes "\<And>j. j \<le> max i li \<Longrightarrow> \<tau> \<sigma> j = \<tau> \<sigma>' j"
  shows "check_upt_LTP_p \<sigma> I li xs i = check_upt_LTP_p \<sigma>' I li xs i"
proof -
  have "li + length ys \<le> i \<Longrightarrow> Suc n \<le> \<delta> \<sigma>' i (li + length ys) \<Longrightarrow>
    (Suc (li + length ys)) \<le> i" for ys :: "nat list" and n
    by (cases "li + length ys = i") auto
  then show ?thesis
    using assms
    by (fastforce simp: check_upt_LTP_p_def Let_def simp del: upt.simps split: list.splits nat.splits)
qed

lemma check_upt_LTP_p_eq:
  assumes "\<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i"
  shows "xs = [li..<Suc (LTP_p \<sigma> i I)] \<longleftrightarrow> check_upt_LTP_p \<sigma> I li xs i"
proof -
  have "li + length xs = Suc (LTP_p \<sigma> i I) \<longleftrightarrow> li + length xs - 1 = LTP_p \<sigma> i I" if "xs \<noteq> []"
    using that
    by (cases xs) auto
  then have "xs = [li..<Suc (LTP_p \<sigma> i I)] \<longleftrightarrow> (xs = [] \<and> LTP_p \<sigma> i I < li) \<or>
    (xs \<noteq> [] \<and> xs = [li..<li + length xs] \<and> li + length xs - 1 = LTP_p \<sigma> i I)"
    by auto
  moreover have "\<dots> \<longleftrightarrow> (xs = [] \<and>
    (case left I of 0 \<Rightarrow> i < li | Suc n \<Rightarrow>
      (if \<not> li \<le> i \<and> left I = 0 then 0 < \<delta> \<sigma> li i else \<delta> \<sigma> i li < left I))) \<or>
    (xs \<noteq> [] \<and> xs = [li..<li + length xs] \<and>
    (case left I of 0 \<Rightarrow> li + length xs - 1 = i | Suc n \<Rightarrow>
      (case left I of 0 \<Rightarrow> i \<le> li + length xs - 1 \<and>
        \<delta> \<sigma> (li + length xs - 1) i = 0 \<and> 0 < \<delta> \<sigma> (Suc (li + length xs - 1)) (li + length xs - 1)
      | Suc n \<Rightarrow> li + length xs - 1 \<le> i \<and>
        left I \<le> \<delta> \<sigma> i (li + length xs - 1) \<and> \<delta> \<sigma> i (Suc (li + length xs - 1)) < left I)))"
    using LTP_p_def[OF assms, symmetric]
    unfolding LTP_minus_lt_iff[OF assms, symmetric]
    unfolding LTP_minus_eq_iff[OF assms, symmetric]
    by (auto split: nat.splits)
  moreover have "\<dots> \<longleftrightarrow> (case xs of [] \<Rightarrow>
    (case left I of 0 \<Rightarrow> i < li | Suc n \<Rightarrow>
      (if \<not> li \<le> i \<and> left I = 0 then 0 < \<delta> \<sigma> li i else \<delta> \<sigma> i li < left I))
    | _ \<Rightarrow> xs = [li..<li + length xs] \<and>
      (case left I of 0 \<Rightarrow> li + length xs - 1 = i | Suc n \<Rightarrow>
        (li + length xs - 1 \<le> i \<and> left I \<le> \<delta> \<sigma> i (li + length xs - 1) \<and> \<delta> \<sigma> i (li + length xs) < left I)))"
    by (auto split: nat.splits list.splits)
  ultimately show ?thesis
    unfolding check_upt_LTP_p_def
    by simp
qed

lemma v_check_exec_Once_code[code]: "v_check_exec \<sigma> vs (Formula.Once I \<phi>) vp = (case vp of
  VOnce i li vps \<Rightarrow>
    (case right I of \<infinity> \<Rightarrow> li = 0 | enat b \<Rightarrow> ((li = 0 \<or> b < \<delta> \<sigma> i (li - 1)) \<and> \<delta> \<sigma> i li \<le> b)) 
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> check_upt_LTP_p \<sigma> I li (map v_at vps) i \<and> Ball (set vps) (v_check_exec \<sigma> vs \<phi>)
  | VOnceOut i \<Rightarrow> \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I 
  | _ \<Rightarrow> False)"
  by (auto simp: Let_def check_upt_LTP_p_eq ETP_minus_le_iff ETP_minus_eq_iff split: vproof.splits enat.splits simp del: upt_Suc)

lemma s_check_exec_Historically_code[code]: "s_check_exec \<sigma> vs (Formula.Historically I \<phi>) vp = (case vp of
  SHistorically i li vps \<Rightarrow>
    (case right I of \<infinity> \<Rightarrow> li = 0 | enat b \<Rightarrow> ((li = 0 \<or> b < \<delta> \<sigma> i (li - 1)) \<and> \<delta> \<sigma> i li \<le> b))
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> check_upt_LTP_p \<sigma> I li (map s_at vps) i \<and> Ball (set vps) (s_check_exec \<sigma> vs \<phi>)
  | SHistoricallyOut i \<Rightarrow> \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I 
  | _ \<Rightarrow> False)"
  by (auto simp: Let_def check_upt_LTP_p_eq ETP_minus_le_iff ETP_minus_eq_iff split: sproof.splits enat.splits simp del: upt_Suc)

lemma v_check_exec_Since_code[code]: "v_check_exec \<sigma> vs (Formula.Since \<phi> I \<psi>) vp = (case vp of
  VSince i vp1 vp2s \<Rightarrow>
    let j = v_at vp1 in
    (case right I of \<infinity> \<Rightarrow> True | enat b \<Rightarrow> \<delta> \<sigma> i j \<le> b) \<and> j \<le> i
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> check_upt_LTP_p \<sigma> I j (map v_at vp2s) i
    \<and> v_check_exec \<sigma> vs \<phi> vp1 \<and> Ball (set vp2s) (v_check_exec \<sigma> vs \<psi>)
  | VSinceInf i li vp2s \<Rightarrow>
    (case right I of \<infinity> \<Rightarrow> li = 0 | enat b \<Rightarrow> ((li = 0 \<or> b < \<delta> \<sigma> i (li - 1)) \<and> \<delta> \<sigma> i li \<le> b)) \<and>
    \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i \<and>
     check_upt_LTP_p \<sigma> I li (map v_at vp2s) i \<and> Ball (set vp2s) (v_check_exec \<sigma> vs \<psi>)
  | VSinceOut i \<Rightarrow> \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I 
  | _ \<Rightarrow> False)"
  by (auto simp: Let_def check_upt_LTP_p_eq ETP_minus_le_iff ETP_minus_eq_iff split: vproof.splits enat.splits simp del: upt_Suc)

lemma ETP_f_le_iff: "max i (ETP \<sigma> (\<tau> \<sigma> i + a)) \<le> j \<longleftrightarrow> i \<le> j \<and> \<delta> \<sigma> j i \<ge> a"
  by (metis add.commute max.bounded_iff \<tau>_mono i_ETP_tau le_diff_conv2)

lemma ETP_f_ge_iff: "j \<le> max i (ETP \<sigma> (\<tau> \<sigma> i + n)) \<longleftrightarrow> (case n of 0 \<Rightarrow> j \<le> i
  | Suc n' \<Rightarrow> (case j of 0 \<Rightarrow> True | Suc j' \<Rightarrow> \<delta> \<sigma> j' i < n))"
proof (cases n)
  case 0
  then show ?thesis
    by (auto simp: max_def) (metis i_ge_etpi verit_la_disequality)
next
  case (Suc n')
  have max: "max i (ETP \<sigma> (\<tau> \<sigma> i + n)) = ETP \<sigma> (\<tau> \<sigma> i + n)"
    by (auto simp: max_def Suc)
       (metis Groups.ab_semigroup_add_class.add.commute ETP_ge less_or_eq_imp_le plus_1_eq_Suc)
  have "j \<le> max i (ETP \<sigma> (\<tau> \<sigma> i + n)) \<longleftrightarrow> (\<forall>ia. \<tau> \<sigma> i + n \<le> \<tau> \<sigma> ia \<longrightarrow> j \<le> ia)"
    unfolding max
    unfolding ETP_def
    by (meson LeastI_ex Least_le order.trans ex_le_\<tau>)
  moreover have "\<dots> \<longleftrightarrow> (case j of 0 \<Rightarrow> True | Suc j' \<Rightarrow> \<not>\<tau> \<sigma> i + n \<le> \<tau> \<sigma> j')"
    by (auto split: nat.splits) (meson i_ETP_tau le_trans not_less_eq_eq)
  moreover have "\<dots> \<longleftrightarrow> (case j of 0 \<Rightarrow> True | Suc j' \<Rightarrow> \<delta> \<sigma> j' i < n)"
    by (auto simp: Suc split: nat.splits)
  ultimately show ?thesis
    by (auto simp: Suc)
qed

definition "check_upt_ETP_f \<sigma> I i xs hi \<longleftrightarrow> (let j = Suc hi - length xs in
  (case xs of [] \<Rightarrow> (case left I of 0 \<Rightarrow> Suc hi \<le> i | Suc n' \<Rightarrow> \<delta> \<sigma> hi i < left I)
  | _ \<Rightarrow> (xs = [j..<Suc hi] \<and>
  (case left I of 0 \<Rightarrow> j \<le> i | Suc n' \<Rightarrow>
  (case j of 0 \<Rightarrow> True | Suc j' \<Rightarrow> \<delta> \<sigma> j' i < left I)) \<and>
  i \<le> j \<and> left I \<le> \<delta> \<sigma> j i)))"

lemma check_upt_lu_cong:
  assumes "\<And>j. min i hi \<le> j \<and> j \<le> max i hi \<Longrightarrow> \<tau> \<sigma> j = \<tau> \<sigma>' j"
  shows "check_upt_ETP_f \<sigma> I i xs hi = check_upt_ETP_f \<sigma>' I i xs hi"
  using assms
  unfolding check_upt_ETP_f_def
  by (auto simp add: Let_def le_Suc_eq split: list.splits nat.splits)

lemma check_upt_ETP_f_eq: "xs = [ETP_f \<sigma> i I..<Suc hi] \<longleftrightarrow> check_upt_ETP_f \<sigma> I i xs hi"
proof -
  have F1: "(case left I of 0 \<Rightarrow> Suc hi \<le> i | Suc n' \<Rightarrow> \<delta> \<sigma> hi i < left I) =
    (Suc hi \<le> ETP_f \<sigma> i I)"
    unfolding ETP_f_ge_iff[where ?j="Suc hi" and ?n="left I"]
    by (auto split: nat.splits)
  have "xs = [ETP_f \<sigma> i I..<Suc hi] \<longleftrightarrow> (let j = Suc hi - length xs in
    (xs = [] \<and> (case left I of 0 \<Rightarrow> Suc hi \<le> i | Suc n' \<Rightarrow> \<delta> \<sigma> hi i < left I)) \<or>
    (xs \<noteq> [] \<and> xs = [j..<Suc hi] \<and>
    (case left I of 0 \<Rightarrow> j \<le> i | Suc n' \<Rightarrow>
    (case j of 0 \<Rightarrow> True | Suc j' \<Rightarrow> \<delta> \<sigma> j' i < left I)) \<and>
    i \<le> j \<and> left I \<le> \<delta> \<sigma> j i))"
    unfolding F1
    unfolding Let_def
    unfolding ETP_f_ge_iff[where ?n="left I", symmetric]
    unfolding ETP_f_le_iff[symmetric]
    unfolding eq_iff[of _ "ETP_f \<sigma> i I", symmetric]
    by auto
  moreover have "\<dots> \<longleftrightarrow> (let j = Suc hi - length xs in
    (case xs of [] \<Rightarrow> (case left I of 0 \<Rightarrow> Suc hi \<le> i | Suc n' \<Rightarrow> \<delta> \<sigma> hi i < left I)
    | _ \<Rightarrow> (xs = [j..<Suc hi] \<and>
    (case left I of 0 \<Rightarrow> j \<le> i | Suc n' \<Rightarrow>
    (case j of 0 \<Rightarrow> True | Suc j' \<Rightarrow> \<delta> \<sigma> j' i < left I)) \<and>
    i \<le> j \<and> left I \<le> \<delta> \<sigma> j i)))"
    by (auto simp: Let_def split: list.splits)
  finally show ?thesis
    unfolding check_upt_ETP_f_def .
qed

lemma v_check_exec_Eventually_code[code]: "v_check_exec \<sigma> vs (Formula.Eventually I \<phi>) vp = (case vp of
  VEventually i hi vps \<Rightarrow>
    (case right I of \<infinity> \<Rightarrow> False | enat b \<Rightarrow> (\<delta> \<sigma> hi i \<le> b \<and> b < \<delta> \<sigma> (Suc hi) i)) \<and>
     check_upt_ETP_f \<sigma> I i (map v_at vps) hi \<and> Ball (set vps) (v_check_exec \<sigma> vs \<phi>)
  | _ \<Rightarrow> False)"
  by (auto simp: Let_def LTP_plus_ge_iff LTP_plus_eq_iff check_upt_ETP_f_eq simp del: upt_Suc
      split: vproof.splits enat.splits)

lemma s_check_exec_Always_code[code]: "s_check_exec \<sigma> vs (Formula.Always I \<phi>) sp = (case sp of
  SAlways i hi sps \<Rightarrow>
    (case right I of \<infinity> \<Rightarrow> False | enat b \<Rightarrow> (\<delta> \<sigma> hi i \<le> b \<and> b < \<delta> \<sigma> (Suc hi) i)) 
    \<and> check_upt_ETP_f \<sigma> I i (map s_at sps) hi \<and> Ball (set sps) (s_check_exec \<sigma> vs \<phi>)
  | _ \<Rightarrow> False)"
  by (auto simp: Let_def LTP_plus_ge_iff LTP_plus_eq_iff check_upt_ETP_f_eq simp del: upt_Suc
      split: sproof.splits enat.splits)

lemma v_check_exec_Until_code[code]: "v_check_exec \<sigma> vs (Formula.Until \<phi> I \<psi>) vp = (case vp of
  VUntil i vp2s vp1 \<Rightarrow>
    let j = v_at vp1 in 
    (case right I of \<infinity> \<Rightarrow> True | enat b \<Rightarrow> j < LTP_f \<sigma> i b)
    \<and> i \<le> j \<and> check_upt_ETP_f \<sigma> I i (map v_at vp2s) j
    \<and> v_check_exec \<sigma> vs \<phi> vp1 \<and> Ball (set vp2s) (v_check_exec \<sigma> vs \<psi>)
 | VUntilInf i hi vp2s \<Rightarrow>
    (case right I of \<infinity> \<Rightarrow> False | enat b \<Rightarrow> (\<delta> \<sigma> hi i \<le> b \<and> b < \<delta> \<sigma> (Suc hi) i)) \<and>
     check_upt_ETP_f \<sigma> I i (map v_at vp2s) hi \<and> Ball (set vp2s) (v_check_exec \<sigma> vs \<psi>)
 | _ \<Rightarrow> False)"
  by (auto simp: Let_def LTP_plus_ge_iff LTP_plus_eq_iff check_upt_ETP_f_eq simp del: upt_Suc
      split: vproof.splits enat.splits)

subsection\<open>ETP/LTP setup\<close>

lemma ETP_aux: "\<not> t \<le> \<tau> \<sigma> i \<Longrightarrow> i \<le> (LEAST i. t \<le> \<tau> \<sigma> i)"
  by (meson LeastI_ex \<tau>_mono ex_le_\<tau> nat_le_linear order_trans)

function ETP_rec where
  "ETP_rec \<sigma> t i = (if \<tau> \<sigma> i \<ge> t then i else ETP_rec \<sigma> t (i + 1))"
  by pat_completeness auto
termination
  using ETP_aux
  by (relation "measure (\<lambda>(\<sigma>, t, i). Suc (ETP \<sigma> t) - i)")
    (fastforce simp: ETP_def)+

lemma ETP_rec_sound: "ETP_rec \<sigma> t j = (LEAST i. i \<ge> j \<and> t \<le> \<tau> \<sigma> i)"
proof (induction \<sigma> t j rule: ETP_rec.induct)
  case (1 \<sigma> t i)
  show ?case
  proof (cases "\<tau> \<sigma> i \<ge> t")
    case True
    then show ?thesis
      by simp (metis (no_types, lifting) Least_equality order_refl)
  next
    case False
    then show ?thesis
      using 1[OF False]
      by (simp add: ETP_rec.simps[of _ _ i] del: ETP_rec.simps)
         (metis Suc_leD le_antisym not_less_eq_eq)
  qed
qed

lemma ETP_code[code]: "ETP \<sigma> t = ETP_rec \<sigma> t 0"
  using ETP_rec_sound[of \<sigma> t 0]
  by (auto simp: ETP_def)

lemma LTP_aux:
  assumes "\<tau> \<sigma> (Suc i) \<le> t"
  shows "i \<le> Max {i. \<tau> \<sigma> i \<le> t}"
proof -
  have "finite {i. \<tau> \<sigma> i \<le> t}"
    by (smt (verit, del_insts) \<tau>_mono finite_nat_set_iff_bounded_le i_LTP_tau le0 le_trans mem_Collect_eq) 
  moreover have "i \<in> {i. \<tau> \<sigma> i \<le> t}"
    using le_trans[OF \<tau>_mono[of i "Suc i" \<sigma>] assms]
    by auto
  ultimately show ?thesis
    by (rule Max_ge)
qed

function (sequential) LTP_rec where
  "LTP_rec \<sigma> t i = (if \<tau> \<sigma> (Suc i) \<le> t then LTP_rec \<sigma> t (i + 1) else i)"
  by pat_completeness auto
termination
  using LTP_aux
  by (relation "measure (\<lambda>(\<sigma>, t, i). Suc (LTP \<sigma> t) - i)") (fastforce simp: LTP_def)+

lemma LTP_rec_sound: "LTP_rec \<sigma> t j = Max ({i. i \<ge> j \<and> (\<tau> \<sigma> i) \<le> t} \<union> {j})"
proof (induction \<sigma> t j rule: LTP_rec.induct)
  case (1 \<sigma> t j)
  have fin: "finite {i. j \<le> i \<and> \<tau> \<sigma> i \<le> t}"
    by (smt (verit, del_insts) \<tau>_mono finite_nat_set_iff_bounded_le i_LTP_tau le0 le_trans
        mem_Collect_eq)
  show ?case
  proof (cases "\<tau> \<sigma> (Suc j) \<le> t")
    case True
    have diffI: "{i. Suc j \<le> i \<and> \<tau> \<sigma> i \<le> t} = {i. j \<le> i \<and> \<tau> \<sigma> i \<le> t} - {j}"
      by auto
    show ?thesis
      using 1[OF True] True fin
      by (auto simp del: LTP_rec.simps simp add: LTP_rec.simps[of _ _ j] diffI intro: max_aux)
  next
    case False
    then show ?thesis
      using fin
      by (auto simp: not_le intro!: Max_insert2[symmetric]
        dest!: order.strict_trans1 less_\<tau>D)
  qed
qed

lemma LTP_code[code]: "LTP \<sigma> t = (if t < \<tau> \<sigma> 0
  then Code.abort (STR ''LTP: undefined'') (\<lambda>_. LTP \<sigma> t)
  else LTP_rec \<sigma> t 0)"
  using LTP_rec_sound[of \<sigma> t 0]
  by (auto simp: LTP_def insert_absorb simp del: LTP_rec.simps)

lemma map_part_code[code]: "Rep_part (map_part f xs) = map (map_prod id f) (Rep_part xs)"
  using Rep_part[of xs]
  by (auto simp: map_part_def intro!: Abs_part_inverse)

lemma coset_subset_set_code[code]:
  "(List.coset (xs :: _ :: universe list) \<subseteq> set ys) = (case universe of None \<Rightarrow> False
  | Some zs \<Rightarrow> \<forall>z \<in> set zs. z \<in> set xs \<or> z \<in> set ys)"
  using finite_compl finite_subset
  by (auto split: option.splits dest!: infinite finite)

lemma is_empty_coset[code]: "Set.is_empty (List.coset (xs :: _ :: universe list)) =
  (case universe of None \<Rightarrow> False
  | Some zs \<Rightarrow> \<forall>z \<in> set zs. z \<in> set xs)"
  using coset_subset_set_code[of xs] by (auto simp: Set.is_empty_def split: option.splits dest: infinite finite)

subsection \<open>Exported functions\<close>

type_synonym name = string8

declare Formula.future_bounded.simps[code]

definition collect_paths :: "('n, 'd :: {default, linorder}) trace \<Rightarrow> ('n, 'd) formula \<Rightarrow> ('n, 'd) expl \<Rightarrow> 'd set list set option" where
  "collect_paths \<sigma> \<phi> e = (if (distinct_paths e \<and> check_all_aux \<sigma> (\<lambda>_. UNIV) \<phi> e) then None else Some (collect_paths_aux {[]} \<sigma> (\<lambda>_. UNIV) \<phi> e))"

definition check :: "(name, event_data) trace \<Rightarrow> (name, event_data) formula \<Rightarrow> (name, event_data) expl \<Rightarrow> bool" where
  "check = check_all"

definition collect_paths_specialized :: "(name, event_data) trace \<Rightarrow> (name, event_data) formula \<Rightarrow> (name, event_data) expl \<Rightarrow> event_data set list set option" where
  "collect_paths_specialized = collect_paths"

definition trace_of_list_specialized :: "((name \<times> event_data list) set \<times> nat) list \<Rightarrow> (name, event_data) trace" where
  "trace_of_list_specialized xs = trace_of_list xs"

definition specialized_set :: "(name \<times> event_data list) list \<Rightarrow> (name \<times> event_data list) set" where
  "specialized_set = set"

definition ed_set :: "event_data list \<Rightarrow> event_data set" where
  "ed_set = set"

definition sum_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sum_nat m n = m + n"

definition sub_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sub_nat m n = m - n"

lift_definition abs_part :: "(event_data set \<times> 'a) list \<Rightarrow> (event_data, 'a) part" is
  "\<lambda>xs.
   let Ds = map fst xs in
   if {} \<in> set Ds
   \<or> (\<exists>D \<in> set Ds. \<exists>E \<in> set Ds. D \<noteq> E \<and> D \<inter> E \<noteq> {})
   \<or> \<not> distinct Ds
   \<or> (\<Union>D \<in> set Ds. D) \<noteq> UNIV then [(UNIV, undefined)] else xs"
  by (auto simp: partition_on_def disjoint_def)

export_code interval enat nat_of_integer integer_of_nat
  STT Formula.TT Inl EInt Formula.Var Leaf set part_hd sum_nat sub_nat subsvals
  check trace_of_list_specialized specialized_set ed_set abs_part 
  collect_paths_specialized
  in OCaml module_name Checker file_prefix "checker"

(*<*)
end
(*>*)
