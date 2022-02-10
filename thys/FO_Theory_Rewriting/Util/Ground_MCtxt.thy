theory Ground_MCtxt
  imports
   Multihole_Context
   Regular_Tree_Relations.Ground_Terms
   Regular_Tree_Relations.Ground_Ctxt
begin

subsection \<open>Ground multihole context\<close>

datatype (gfuns_mctxt: 'f) gmctxt = GMHole | GMFun 'f "'f gmctxt list"

subsubsection \<open>Basic function on ground mutlihole contexts\<close>

primrec gmctxt_of_gterm :: "'f gterm \<Rightarrow> 'f gmctxt" where
  "gmctxt_of_gterm (GFun f ts) = GMFun f (map gmctxt_of_gterm ts)"

fun num_gholes :: "'f gmctxt \<Rightarrow> nat" where
  "num_gholes GMHole = Suc 0"
| "num_gholes (GMFun _ ctxts) = sum_list (map num_gholes ctxts)"

primrec gterm_of_gmctxt :: "'f gmctxt \<Rightarrow> 'f gterm" where
  "gterm_of_gmctxt (GMFun f Cs) = GFun f (map gterm_of_gmctxt Cs)"

primrec term_of_gmctxt :: "'f gmctxt \<Rightarrow> ('f, 'v) term" where
  "term_of_gmctxt (GMFun f Cs) = Fun f (map term_of_gmctxt Cs)"

primrec gmctxt_of_gctxt :: "'f gctxt \<Rightarrow> 'f gmctxt" where
  "gmctxt_of_gctxt \<box>\<^sub>G = GMHole"
| "gmctxt_of_gctxt (GMore f ss C ts) =
    GMFun f (map gmctxt_of_gterm ss @ gmctxt_of_gctxt C # map gmctxt_of_gterm ts)"

fun gctxt_of_gmctxt :: "'f gmctxt \<Rightarrow> 'f gctxt" where
  "gctxt_of_gmctxt GMHole = \<box>\<^sub>G"
| "gctxt_of_gmctxt (GMFun f Cs) = (let n = length (takeWhile (\<lambda> C. num_gholes C = 0) Cs) in
     (if n < length Cs then
        GMore f (map gterm_of_gmctxt (take n Cs)) (gctxt_of_gmctxt (Cs ! n)) (map gterm_of_gmctxt (drop (Suc n) Cs))
      else undefined))"

primrec gmctxt_of_mctxt :: "('f, 'v) mctxt \<Rightarrow> 'f gmctxt" where
   "gmctxt_of_mctxt MHole = GMHole"
|  "gmctxt_of_mctxt (MFun f Cs) = GMFun f (map gmctxt_of_mctxt Cs)"

primrec mctxt_of_gmctxt :: "'f gmctxt \<Rightarrow> ('f, 'v) mctxt" where
   "mctxt_of_gmctxt GMHole = MHole"
|  "mctxt_of_gmctxt (GMFun f Cs) = MFun f (map mctxt_of_gmctxt Cs)"

fun funas_gmctxt where
  "funas_gmctxt (GMFun f Cs) = {(f, length Cs)} \<union> \<Union>(funas_gmctxt ` set Cs)" |
  "funas_gmctxt _ = {}"

abbreviation "partition_gholes xs Cs \<equiv> partition_by xs (map num_gholes Cs)"

fun fill_gholes :: "'f gmctxt \<Rightarrow> 'f gterm list \<Rightarrow> 'f gterm" where
  "fill_gholes GMHole [t] = t"
| "fill_gholes (GMFun f cs) ts = GFun f (map (\<lambda> i. fill_gholes (cs ! i)
    (partition_gholes ts cs ! i)) [0 ..< length cs])"

fun fill_gholes_gmctxt :: "'f gmctxt \<Rightarrow> 'f gmctxt list \<Rightarrow> 'f gmctxt" where
  "fill_gholes_gmctxt GMHole [] = GMHole" |
  "fill_gholes_gmctxt GMHole [t] = t" |
  "fill_gholes_gmctxt (GMFun f cs) ts = (GMFun f (map (\<lambda> i. fill_gholes_gmctxt (cs ! i) 
    (partition_gholes ts cs ! i)) [0 ..< length cs]))"

subsubsection \<open>An inverse of @{term fill_gholes}\<close>
fun unfill_gholes :: "'f gmctxt \<Rightarrow> 'f gterm \<Rightarrow> 'f gterm list" where
  "unfill_gholes GMHole t = [t]"
| "unfill_gholes (GMFun g Cs) (GFun f ts) = (if f = g \<and> length ts = length Cs then
    concat (map (\<lambda>i. unfill_gholes (Cs ! i) (ts ! i)) [0..<length ts]) else undefined)"

fun sup_gmctxt_args :: "'f gmctxt \<Rightarrow> 'f gmctxt \<Rightarrow> 'f gmctxt list" where
  "sup_gmctxt_args GMHole D = [D]" |
  "sup_gmctxt_args C GMHole = replicate (num_gholes C) GMHole" |
  "sup_gmctxt_args (GMFun f Cs) (GMFun g Ds) =
    (if f = g \<and> length Cs = length Ds then concat (map (case_prod sup_gmctxt_args) (zip Cs Ds))
    else undefined)"

fun ghole_poss :: "'f gmctxt \<Rightarrow> pos set" where
  "ghole_poss GMHole = {[]}" |
  "ghole_poss (GMFun f cs) = \<Union>(set (map (\<lambda> i. (\<lambda> p. i # p) ` ghole_poss (cs ! i)) [0 ..< length cs]))"

abbreviation "poss_rec f ts \<equiv> map2 (\<lambda> i t. map ((#) i) (f t)) ([0 ..< length ts]) ts"
fun ghole_poss_list :: "'f gmctxt \<Rightarrow> pos list" where
  "ghole_poss_list GMHole = [[]]"
| "ghole_poss_list (GMFun f cs) = concat (poss_rec ghole_poss_list cs)"


fun poss_gmctxt :: "'f gmctxt \<Rightarrow> pos set" where
  "poss_gmctxt GMHole = {}" |
  "poss_gmctxt (GMFun f cs) = {[]} \<union> \<Union>(set (map (\<lambda> i. (\<lambda> p. i # p) ` poss_gmctxt (cs ! i)) [0 ..< length cs]))"

lemma poss_simps [simp]:
  "ghole_poss (GMFun f Cs) = {i # p | i p. i < length Cs \<and> p \<in> ghole_poss (Cs ! i)}"
  "poss_gmctxt (GMFun f Cs) = {[]} \<union> {i # p | i p. i < length Cs \<and> p \<in> poss_gmctxt (Cs ! i)}"
  by auto

fun ghole_num_bef_pos where
  "ghole_num_bef_pos [] _ = 0" |
  "ghole_num_bef_pos (i # q) (GMFun f Cs) = sum_list (map num_gholes (take i Cs)) + ghole_num_bef_pos q (Cs ! i)"

fun ghole_num_at_pos where
  "ghole_num_at_pos [] C = num_gholes C" |
  "ghole_num_at_pos (i # q) (GMFun f Cs) = ghole_num_at_pos q (Cs ! i)"

fun subgm_at :: "'f gmctxt \<Rightarrow> pos \<Rightarrow> 'f gmctxt" where
  "subgm_at C [] = C"
| "subgm_at (GMFun f Cs) (i # p) = subgm_at (Cs ! i) p"

definition gmctxt_subtgm_at_fill_args where
  "gmctxt_subtgm_at_fill_args p C ts = take (ghole_num_at_pos p C) (drop (ghole_num_bef_pos p C) ts)"

(*
declare hole_poss.simps(2)[simp del]
declare poss_mctxt.simps(2)[simp del]
*)

instantiation gmctxt :: (type) inf
begin

fun inf_gmctxt :: "'a gmctxt \<Rightarrow> 'a gmctxt \<Rightarrow> 'a gmctxt" where
  "GMHole \<sqinter> D = GMHole" |
  "C \<sqinter> GMHole = GMHole" |
  "GMFun f Cs \<sqinter> GMFun g Ds =
    (if f = g \<and> length Cs = length Ds then GMFun f (map (case_prod (\<sqinter>)) (zip Cs Ds))
    else GMHole)"

instance ..
end

instantiation gmctxt :: (type) sup
begin

fun sup_gmctxt :: "'a gmctxt \<Rightarrow> 'a gmctxt \<Rightarrow> 'a gmctxt" where
  "GMHole \<squnion> D = D" |
  "C \<squnion> GMHole = C" |
  "GMFun f Cs \<squnion> GMFun g Ds =
    (if f = g \<and> length Cs = length Ds then GMFun f (map (case_prod (\<squnion>)) (zip Cs Ds))
    else undefined)"

instance ..
end

subsubsection \<open>Orderings and compatibility of ground multihole contexts\<close>

inductive less_eq_gmctxt :: "'f gmctxt \<Rightarrow> 'f gmctxt \<Rightarrow> bool" where
 base [simp]: "less_eq_gmctxt GMHole u"
| ind[intro]: "length cs = length ds \<Longrightarrow> (\<And>i. i < length cs \<Longrightarrow> less_eq_gmctxt (cs ! i) (ds ! i)) \<Longrightarrow>
     less_eq_gmctxt (GMFun f cs) (GMFun f ds)"

inductive_set comp_gmctxt :: "('f gmctxt \<times> 'f gmctxt) set" where
  GMHole1 [simp]: "(GMHole, D) \<in> comp_gmctxt" |
  GMHole2 [simp]: "(C, GMHole) \<in> comp_gmctxt" |
  GMFun [intro]: "f = g \<Longrightarrow> length Cs = length Ds \<Longrightarrow> \<forall>i < length Ds. (Cs ! i, Ds ! i) \<in> comp_gmctxt \<Longrightarrow>
    (GMFun f Cs, GMFun g Ds) \<in> comp_gmctxt"

definition gmctxt_closing where
  "gmctxt_closing C D \<longleftrightarrow> less_eq_gmctxt C D \<and> ghole_poss D \<subseteq> ghole_poss C"


inductive eq_gfill ("(_/ =\<^sub>G\<^sub>f _)" [51, 51] 50) where
  eqfI [intro]: "t = fill_gholes D ss \<Longrightarrow> num_gholes D = length ss \<Longrightarrow> t =\<^sub>G\<^sub>f (D, ss)"

subsubsection \<open>Conversions from and to ground multihole contexts\<close>

lemma num_gholes_o_gmctxt_of_gterm [simp]:
  "num_gholes \<circ> gmctxt_of_gterm = (\<lambda>x. 0)"
  by (rule ext, induct_tac x) simp_all

lemma mctxt_of_term_term_of_mctxt_id [simp]:
  "num_gholes C = 0 \<Longrightarrow> gmctxt_of_gterm (gterm_of_gmctxt C) = C"
  by (induct C) (simp_all add: map_idI)

lemma num_holes_mctxt_of_term [simp]:
  "num_gholes (gmctxt_of_gterm t) = 0"
  by (induct t) simp_all

lemma num_gholes_gmctxt_of_mctxt [simp]:
  "ground_mctxt C \<Longrightarrow> num_gholes (gmctxt_of_mctxt C) = num_holes C"
  by (induct C) (auto intro: nth_sum_listI)

lemma num_holes_mctxt_of_gmctxt [simp]:
  "num_holes (mctxt_of_gmctxt C) = num_gholes C"
  by (induct C) (auto intro: nth_sum_listI)

lemma num_holes_mctxt_of_gmctxt_fun_comp [simp]:
  "num_holes \<circ> mctxt_of_gmctxt = num_gholes"
  by (auto simp: comp_def)

lemma gmctxt_of_gctxt_num_gholes [simp]:
  "num_gholes (gmctxt_of_gctxt C) = Suc 0"
  by (induct C) auto

lemma ground_mctxt_list_num_gholes_gmctxt_of_mctxt_conv [simp]:
  "\<forall>x\<in>set Cs. ground_mctxt x \<Longrightarrow> map (num_gholes \<circ> gmctxt_of_mctxt) Cs = map num_holes Cs"
  by auto


lemma num_gholes_map_gmctxt [simp]:
  "num_gholes (map_gmctxt f C) = num_gholes C"
  by (induct C)  (auto simp: comp_def, metis (no_types, lifting) map_eq_conv)

lemma map_num_gholes_map_gmctxt [simp]:
  "map (num_gholes \<circ> map_gmctxt f) Cs = map num_gholes Cs"
  by (induct Cs) auto

lemma gterm_of_gmctxt_gmctxt_of_gterm_id [simp]:
  "gterm_of_gmctxt (gmctxt_of_gterm t) = t"
  by (induct t) (simp_all add: map_idI)

lemma no_gholes_gmctxt_of_gterm_gterm_of_gmctxt_id [simp]:
  "num_gholes C = 0 \<Longrightarrow> gmctxt_of_gterm (gterm_of_gmctxt C) = C"
  by (induct C) (auto simp: comp_def intro: nth_equalityI)

lemma no_gholes_term_of_gterm_gterm_of_gmctxt [simp]:
  "num_gholes C = 0 \<Longrightarrow> term_of_gterm (gterm_of_gmctxt C) = term_of_gmctxt C"
  by (induct C) (auto simp: comp_def intro: nth_equalityI)

lemma no_gholes_term_of_mctxt_mctxt_of_gmctxt [simp]:
  "num_gholes C = 0 \<Longrightarrow> term_of_mctxt (mctxt_of_gmctxt C) = term_of_gmctxt C"
  by (induct C) (auto simp: comp_def intro: nth_equalityI)

lemma nthWhile_gmctxt_of_gctxt [simp]:
  "length (takeWhile (\<lambda>C. num_gholes C = 0) (map gmctxt_of_gterm ss @ gmctxt_of_gctxt C # ts)) = length ss"
  by (induct ss) auto

lemma sum_list_nthWhile_length [simp]:
  "sum_list (map num_gholes Cs) = Suc 0 \<Longrightarrow> length (takeWhile (\<lambda>C. num_gholes C = 0) Cs) < length Cs"
  by (induct Cs) auto

lemma gctxt_of_gmctxt_gmctxt_of_gctxt [simp]:
  "gctxt_of_gmctxt (gmctxt_of_gctxt C) = C"
  by (induct C) (auto simp: Let_def comp_def nth_append)

lemma gmctxt_of_gctxt_GMHole_Hole:
  "gmctxt_of_gctxt C = GMHole \<Longrightarrow> C = \<box>\<^sub>G"
  by (metis gctxt_of_gmctxt.simps(1) gctxt_of_gmctxt_gmctxt_of_gctxt)

lemma gmctxt_of_gctxt_gctxt_of_gmctxt:
  "num_gholes C = Suc 0 \<Longrightarrow> gmctxt_of_gctxt (gctxt_of_gmctxt C) = C"
proof (induct C)
  case (GMFun f Cs)
  then obtain i where nth: "i < length Cs" "i = length (takeWhile (\<lambda>C. num_gholes C = 0) Cs)"
    using sum_list_nthWhile_length by auto
  then have "0 < num_gholes (Cs ! i)" unfolding nth(2) using nth_length_takeWhile
    by auto
  from nth(1) this have num: "num_gholes (Cs ! i) = Suc 0" using GMFun(2)
    by (auto elim!: sum_list_1_E)
  then have [simp]: "map (gmctxt_of_gterm \<circ> gterm_of_gmctxt) (drop (Suc i) Cs) = drop (Suc i) Cs" using GMFun(2) nth(1)
    by (auto elim!: sum_list_1_E simp: comp_def intro!: nth_equalityI)
     (metis add.commute add_Suc_right lessI less_diff_conv no_gholes_gmctxt_of_gterm_gterm_of_gmctxt_id not_add_less1)
  have [simp]: "map (gmctxt_of_gterm \<circ> gterm_of_gmctxt) (take i Cs) = take i Cs"
    using nth(1) unfolding nth(2) by (induct Cs) auto
  show ?case using id_take_nth_drop[OF nth(1)]
    by (auto simp: Let_def GMFun(1)[OF nth_mem[OF nth(1)] num] simp flip: nth(2))
qed auto

lemma inj_gmctxt_of_gctxt: "inj gmctxt_of_gctxt"
  unfolding inj_def by (metis gctxt_of_gmctxt_gmctxt_of_gctxt)

lemma inj_gctxt_of_gmctxt_on_single_hole:
  "inj_on gctxt_of_gmctxt (Collect (\<lambda> C. num_gholes C = Suc 0))"
  by (metis (mono_tags, lifting) gmctxt_of_gctxt_gctxt_of_gmctxt inj_onI mem_Collect_eq)

lemma gctxt_of_gmctxt_hole_dest:
  "num_gholes C = Suc 0 \<Longrightarrow> gctxt_of_gmctxt C = \<box>\<^sub>G \<Longrightarrow> C = GMHole"
  by (cases C) (auto simp: Let_def split!: if_splits)

lemma mctxt_of_gmctxt_inv [simp]:
  "gmctxt_of_mctxt (mctxt_of_gmctxt C) = C"
  by (induct C) (simp_all add: map_idI)

lemma ground_mctxt_of_gmctxt [simp]:
  "ground_mctxt (mctxt_of_gmctxt C)"
  by (induct C) auto

lemma ground_mctxt_of_gmctxt' [simp]:
  "mctxt_of_gmctxt C = MFun f D \<Longrightarrow> ground_mctxt (MFun f D)"
  by (induct C) auto

lemma gmctxt_of_mctxt_inv [simp]:
  "ground_mctxt C \<Longrightarrow> mctxt_of_gmctxt (gmctxt_of_mctxt C) = C"
  by (induct C) (auto 0 0 intro!: nth_equalityI)

lemma ground_mctxt_of_gmctxtD:
  "ground_mctxt C \<Longrightarrow> \<exists> D. C = mctxt_of_gmctxt D"
  by (metis gmctxt_of_mctxt_inv)

lemma inj_mctxt_of_gmctxt: "inj_on mctxt_of_gmctxt X"
  by (metis inj_on_def mctxt_of_gmctxt_inv)

lemma inj_gmctxt_of_mctxt_ground:
  "inj_on gmctxt_of_mctxt (Collect ground_mctxt)"
  using gmctxt_of_mctxt_inv inj_on_def by force

lemma map_gmctxt_comp [simp]:
  "map_gmctxt f (map_gmctxt g C) = map_gmctxt (f \<circ> g) C"
  by (induct C) auto

lemma map_mctxt_of_gmctxt:
  "map_mctxt f (mctxt_of_gmctxt C) = mctxt_of_gmctxt (map_gmctxt f C)"
  by (induct C) auto

lemma map_gmctxt_of_mctxt:
  "ground_mctxt C \<Longrightarrow> map_gmctxt f (gmctxt_of_mctxt C) = gmctxt_of_mctxt (map_mctxt f C)"
  by (induct C) auto

lemma map_gmctxt_nempty [simp]:
  "C \<noteq> GMHole \<Longrightarrow> map_gmctxt f C \<noteq> GMHole"
  by (cases C) auto


lemma vars_mctxt_of_gmctxt [simp]:
  "vars_mctxt (mctxt_of_gmctxt C) = {}"
  by (induct C) auto

lemma vars_mctxt_of_gmctxt_subseteq [simp]:
  "vars_mctxt (mctxt_of_gmctxt C) \<subseteq> Q \<longleftrightarrow> True"
  by auto

subsubsection \<open>Equivalences and simplification rules\<close>

lemma eqgfE:
  assumes "t =\<^sub>G\<^sub>f (D, ss)" shows "t = fill_gholes D ss" "num_gholes D = length ss"
  using assms[unfolded eq_gfill.simps] by auto

lemma eqgf_GMHoleE:
  assumes "t =\<^sub>G\<^sub>f (GMHole, ss)" shows "ss = [t]" using eqgfE[OF assms]
  by (cases ss) auto

lemma eqgf_GMFunE:
  assumes "s =\<^sub>G\<^sub>f (GMFun f Cs, ss)"  
  obtains ts sss where "s = GFun f ts" "length ts = length Cs" "length sss = length Cs" 
  "\<And> i. i < length Cs \<Longrightarrow> ts ! i =\<^sub>G\<^sub>f (Cs ! i, sss ! i)" "ss = concat sss"
proof -
  from eqgfE[OF assms] have fh: "s = fill_gholes (GMFun f Cs) ss" 
    and nh: "sum_list (map num_gholes Cs) = length ss" by auto
  from fh obtain ts where s: "s = GFun f ts" by (cases s, auto)
  from fh[unfolded s] 
  have ts: "ts = map (\<lambda>i. fill_gholes (Cs ! i) (partition_gholes ss Cs ! i)) [0..<length Cs]" 
    (is "_ = map (?f Cs ss) _")
    by auto
  let ?sss = "partition_gholes ss Cs"
  from nh have *: "length ?sss = length Cs"
    "\<And>i. i < length Cs \<Longrightarrow> ts ! i =\<^sub>G\<^sub>f (Cs ! i, ?sss ! i)" "ss = concat ?sss"
    by (auto simp: ts length_partition_by_nth)
  have len: "length ts = length Cs" unfolding ts by auto
  assume ass: "\<And>ts sss. s = GFun f ts \<Longrightarrow>
              length ts = length Cs \<Longrightarrow>
              length sss = length Cs \<Longrightarrow> (\<And>i. i < length Cs \<Longrightarrow> ts ! i =\<^sub>G\<^sub>f (Cs ! i, sss ! i)) \<Longrightarrow> ss = concat sss \<Longrightarrow> thesis"
  show thesis by (rule ass[OF s len *])
qed

lemma partition_holes_subseteq [simp]:
  assumes "sum_list (map num_holes Cs) = length xs" "i < length Cs"
    and "x \<in> set (partition_holes xs Cs ! i)"
  shows "x \<in> set xs"
  using assms partition_by_nth_nth_elem length_partition_by_nth
  by (auto simp: in_set_conv_nth) fastforce

lemma partition_gholes_subseteq [simp]:
  assumes "sum_list (map num_gholes Cs) = length xs" "i < length Cs"
    and "x \<in> set (partition_gholes xs Cs ! i)"
  shows "x \<in> set xs"
  using assms partition_by_nth_nth_elem length_partition_by_nth
  by (auto simp: in_set_conv_nth) fastforce

lemma list_elem_to_partition_nth [elim]:
  assumes "sum_list (map num_gholes Cs) = length xs" "x \<in> set xs"
  obtains i where "i < length Cs" "x \<in> set (partition_gholes xs Cs ! i)" using assms
  by (metis concat_partition_by in_set_idx length_map length_partition_by nth_concat_split nth_mem)

lemma partition_holes_fill_gholes_conv':
  "fill_gholes (GMFun f Cs) ts =
    GFun f (map (case_prod fill_gholes) (zip Cs (partition_gholes ts Cs)))"
  unfolding zip_nth_conv [of Cs "partition_gholes ts Cs", simplified]
    and partition_holes_fill_holes_conv by simp

lemma unfill_gholes_conv:
  assumes "length Cs = length ts"
  shows "unfill_gholes (GMFun f Cs) (GFun f ts) =
    concat (map (case_prod unfill_gholes) (zip Cs ts))" using assms
  by (auto simp: zip_nth_conv [of Cs ts, simplified] comp_def)

lemma partition_holes_fill_gholes_gmctxt_conv:
  "fill_gholes_gmctxt (GMFun f Cs) ts =
    GMFun f [fill_gholes_gmctxt (Cs ! i) (partition_gholes ts Cs ! i). i \<leftarrow> [0 ..< length Cs]]"
  by (simp add: partition_by_nth take_map)

lemma partition_holes_fill_gholes_gmctxt_conv':
  "fill_gholes_gmctxt (GMFun f Cs) ts =
    GMFun f (map (case_prod fill_gholes_gmctxt) (zip Cs (partition_gholes ts Cs)))"
  unfolding zip_nth_conv [of Cs "partition_gholes ts Cs", simplified]
    and partition_holes_fill_gholes_gmctxt_conv by simp

lemma fill_gholes_no_holes [simp]:
  "num_gholes C = 0 \<Longrightarrow> fill_gholes C [] = gterm_of_gmctxt C"
  by (induct C) (auto simp: partition_holes_fill_gholes_conv'
    simp del: fill_gholes.simps intro: nth_equalityI)

lemma fill_gholes_gmctxt_no_holes [simp]:
  "num_gholes C = 0 \<Longrightarrow> fill_gholes_gmctxt C [] = C"
  by (induct C) (auto intro: nth_equalityI)

lemma eqgf_GMFunI:
  assumes "\<And> i. i < length Cs \<Longrightarrow> ss ! i =\<^sub>G\<^sub>f (Cs ! i, ts ! i)"
    and "length Cs = length ss" "length ss = length ts"
  shows "GFun f ss =\<^sub>G\<^sub>f (GMFun f Cs, concat ts)" using assms
  apply (auto simp del: fill_gholes.simps
    simp: partition_holes_fill_gholes_conv' intro!: eq_gfill.intros nth_equalityI)
  apply (metis eqgfE length_map map_nth_eq_conv partition_by_concat_id)
  by (metis eqgfE(2) length_concat nth_map_conv)

lemma length_partition_gholes_nth:
  assumes "sum_list (map num_gholes cs) = length ts"
    and "i < length cs"
  shows "length (partition_gholes ts cs ! i) = num_gholes (cs ! i)"
  using assms by (simp add: length_partition_by_nth)

lemma fill_gholes_induct2[consumes 2, case_names GMHole GMFun]:
  fixes P :: "'f gmctxt \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> bool"
  assumes len1: "num_gholes C = length xs" and len2: "num_gholes C = length ys"
  and Hole: "\<And>x y. P GMHole [x] [y]"
  and Fun: "\<And>f Cs xs ys.  sum_list (map num_gholes Cs) = length xs \<Longrightarrow>
    sum_list (map num_gholes Cs) = length ys \<Longrightarrow>
    (\<And>i. i < length Cs \<Longrightarrow> P (Cs ! i) (partition_gholes xs Cs ! i) (partition_gholes ys Cs ! i)) \<Longrightarrow>
    P (GMFun f Cs) (concat (partition_gholes xs Cs)) (concat (partition_gholes ys Cs))"
  shows "P C xs ys"
proof (insert len1 len2, induct C arbitrary: xs ys)
  case GMHole
  then show ?case using Hole by (cases xs; cases ys) auto
next
  case (GMFun f Cs)
  then show ?case using Fun[of Cs xs ys f] by (auto simp: length_partition_by_nth)
qed

lemma fill_gholes_induct[consumes 1, case_names GMHole GMFun]:
  fixes P :: "'f gmctxt \<Rightarrow> 'a list \<Rightarrow> bool"
  assumes len: "num_gholes C = length xs"
    and Hole: "\<And>x. P GMHole [x]"
    and Fun: "\<And>f Cs xs. sum_list (map num_gholes Cs) = length xs \<Longrightarrow>
      (\<And>i. i < length Cs \<Longrightarrow> P (Cs ! i) (partition_gholes xs Cs ! i)) \<Longrightarrow>
      P (GMFun f Cs) (concat (partition_gholes xs Cs))"
  shows "P C xs"
  using fill_gholes_induct2[of C xs xs "\<lambda> C xs _. P C xs"] assms by simp

lemma eq_gfill_induct [consumes 1, case_names GMHole GMFun]:
  assumes "t =\<^sub>G\<^sub>f (C, ts)"
    and "\<And>t. P t GMHole [t]"
    and "\<And>f ss Cs ts. \<lbrakk>length Cs = length ss; sum_list (map num_gholes Cs) = length ts;
      \<forall>i < length ss. ss ! i =\<^sub>G\<^sub>f (Cs ! i, partition_gholes ts Cs ! i) \<and>
        P (ss ! i) (Cs ! i) (partition_gholes ts Cs ! i)\<rbrakk>
      \<Longrightarrow> P (GFun f ss) (GMFun f Cs) ts"
  shows "P t C ts" using assms(1)
proof (induct t arbitrary: C ts)
  case (GFun f ss)
  {assume "C = GMHole" and "ts = [GFun f ss]"
    then have ?case using assms(2) by auto}
  moreover
  {fix Cs
    assume C: "C = GMFun f Cs" and "sum_list (map num_gholes Cs) = length ts"
      and "length Cs = length ss"
      and "GFun f ss = fill_gholes (GMFun f Cs) ts"
    moreover then have "\<forall>i < length ss. ss ! i =\<^sub>G\<^sub>f (Cs ! i, partition_gholes ts Cs ! i)"
      by (auto simp del: fill_gholes.simps
         simp: partition_holes_fill_gholes_conv' length_partition_gholes_nth  intro!: eq_gfill.intros)
    moreover have "\<forall>i < length ss. P (ss ! i) (Cs ! i) (partition_gholes ts Cs ! i)"
      using GFun calculation(5) nth_mem by blast
    ultimately have ?case using assms(3)[of Cs ss ts f] by auto}
  ultimately show ?case using GFun
    by (elim eq_gfill.cases) (auto simp del: fill_gholes.simps,
      metis GFun.prems eqgf_GMFunE eqgf_GMHoleE gterm.inject num_gholes.elims)
qed

lemma nempty_ground_mctxt_gmctxt [simp]:
  "C \<noteq> MHole \<Longrightarrow> ground_mctxt C \<Longrightarrow> gmctxt_of_mctxt C \<noteq> GMHole"
  by (induct C) auto

lemma mctxt_of_gmctxt_fill_holes [simp]:
  assumes "num_gholes C = length ss"
  shows "gterm_of_term (fill_holes (mctxt_of_gmctxt C) (map term_of_gterm ss)) = fill_gholes C ss" using assms
  by (induct rule: fill_gholes_induct) auto

lemma mctxt_of_gmctxt_terms_fill_holes:
  assumes "num_gholes C = length ss"
  shows "gterm_of_term (fill_holes (mctxt_of_gmctxt C) ss) = fill_gholes C (map gterm_of_term ss)" using assms
  by (induct rule: fill_gholes_induct) auto

lemma ground_gmctxt_of_mctxt_gterm_fill_holes:
  assumes "num_holes C = length ss" and "ground_mctxt C"
  shows "term_of_gterm (fill_gholes (gmctxt_of_mctxt C) ss) = fill_holes C (map term_of_gterm ss)" using assms
  by (induct rule: fill_holes_induct)
   (auto simp: comp_def, metis (no_types, lifting) map_eq_conv num_gholes_gmctxt_of_mctxt)

lemma  ground_gmctxt_of_gterm_of_term:
  assumes "num_holes C = length ss" and "ground_mctxt C"
  shows "gterm_of_term (fill_holes C (map term_of_gterm ss)) = fill_gholes (gmctxt_of_mctxt C) ss" using assms
  by (induct rule: fill_holes_induct)
   (auto simp: comp_def, metis (no_types, lifting) map_eq_conv num_gholes_gmctxt_of_mctxt)

lemma ground_gmctxt_of_mctxt_fill_holes [simp]:
  assumes "num_holes C = length ss" and "ground_mctxt C" "\<forall> s \<in> set ss. ground s"  
  shows "term_of_gterm (fill_gholes (gmctxt_of_mctxt C) (map gterm_of_term ss)) = fill_holes C ss" using assms
  by (induct rule: fill_holes_induct) auto

lemma fill_holes_mctxt_of_gmctxt_to_fill_gholes:
  assumes "num_gholes C = length ss"
  shows "fill_holes (mctxt_of_gmctxt C) (map term_of_gterm ss) = term_of_gterm (fill_gholes C ss)"
  using assms
  by (metis ground_gmctxt_of_mctxt_gterm_fill_holes ground_mctxt_of_gmctxt mctxt_of_gmctxt_inv num_holes_mctxt_of_gmctxt)

lemma fill_gholes_gmctxt_of_gterm [simp]:
  "fill_gholes (gmctxt_of_gterm s) [] = s"
  by (induct s) (auto simp add: map_nth_eq_conv)

lemma fill_gholes_GMHole [simp]:
  "length ss = Suc 0 \<Longrightarrow> fill_gholes GMHole ss = ss ! 0"
  by (cases ss) auto

lemma apply_gctxt_fill_gholes:
  "C\<langle>s\<rangle>\<^sub>G = fill_gholes (gmctxt_of_gctxt C) [s]"
  by (induct C) (auto simp: partition_holes_fill_gholes_conv'
    simp del: fill_gholes.simps intro!: nth_equalityI)

lemma fill_gholes_apply_gctxt:
  "num_gholes C = Suc 0 \<Longrightarrow> fill_gholes C [s] = (gctxt_of_gmctxt C)\<langle>s\<rangle>\<^sub>G"
  by (simp add: apply_gctxt_fill_gholes gmctxt_of_gctxt_gctxt_of_gmctxt)


lemma ctxt_of_gctxt_gctxt_of_gmctxt_apply:
  "num_gholes C = Suc 0 \<Longrightarrow> fill_holes (mctxt_of_gmctxt C) [s] = (ctxt_of_gctxt (gctxt_of_gmctxt C))\<langle>s\<rangle>"
proof (induct C)
  case (GMFun f Cs)
  obtain i where split: "i < length Cs" "num_gholes (Cs ! i) = Suc 0"
    "\<forall> j < length Cs. j \<noteq> i \<longrightarrow> num_gholes (Cs ! j) = 0" using GMFun(2)
    by auto
  then have [simp]: "sum_list (take i (map num_gholes Cs)) = 0"
    by (auto simp: sum_list_eq_0_iff dest: set_take_nth)
  from split have [simp]: "j < length Cs \<Longrightarrow> j \<noteq> i \<Longrightarrow>
     fill_holes (mctxt_of_gmctxt (Cs ! j)) [] = term_of_mctxt (mctxt_of_gmctxt (Cs ! j))" for j
    by (intro fill_holes_term_of_mctxt) auto
  from split have [simp]: "gctxt_of_gmctxt (GMFun f Cs) =
    GMore f (map gterm_of_gmctxt (take i Cs)) (gctxt_of_gmctxt (Cs ! i)) (map gterm_of_gmctxt (drop (Suc i) Cs))"
     using nth_length_takeWhile GMFun(2) sum_list_nthWhile_length by (auto simp: Let_def)
  show ?case using GMFun(1)[OF nth_mem[OF split(1)] split(2)] split
    by (auto simp: min_def nth_append_Cons partition_by_nth simp del: gctxt_of_gmctxt.simps intro!: nth_equalityI)
qed auto


lemma fill_gholes_replicate [simp]:
  "n = length ss \<Longrightarrow> fill_gholes (GMFun f (replicate n GMHole)) ss = GFun f ss"
  unfolding partition_holes_fill_gholes_conv'
  by (induct ss arbitrary: n) auto

lemma fill_gholes_gmctxt_replicate_MHole [simp]:
  "fill_gholes_gmctxt C (replicate (num_gholes C) GMHole) = C"
proof (induct C)
  case (GMFun f Cs)
  {fix i assume "i < length Cs"
    then have "partition_gholes (replicate (sum_list (map num_gholes Cs)) GMHole) Cs ! i =
        replicate (num_gholes (Cs ! i)) GMHole"
      using partition_by_nth_nth[of "map num_gholes Cs" "replicate (sum_list (map num_gholes Cs)) MHole"]
      by (auto simp: length_partition_by_nth partition_by_nth_nth intro!: nth_equalityI)}
  note * = this
  show ?case using GMFun[OF nth_mem] by (auto simp: * intro!: nth_equalityI)
qed auto

lemma fill_gholes_gmctxt_GMFun_replicate_length [simp]:
  "fill_gholes_gmctxt (GMFun f (replicate (length Cs) GMHole)) Cs = GMFun f Cs"
  unfolding partition_holes_fill_gholes_gmctxt_conv'
  by (induct Cs) simp_all

lemma fill_gholes_gmctxt_MFun:
  assumes lCs: "length Cs = length ts"
    and lss: "length ss = length ts"
    and rec: "\<And> i. i < length ts \<Longrightarrow> num_gholes (Cs ! i) = length (ss ! i) \<and>
      fill_gholes_gmctxt (Cs ! i) (ss ! i) = ts ! i"
  shows "fill_gholes_gmctxt (GMFun f Cs) (concat ss) = GMFun f ts" 
  using assms unfolding fill_gholes_gmctxt.simps gmctxt.simps
  by (auto intro!: nth_equalityI)
    (metis length_map map_nth_eq_conv partition_by_concat_id)

lemma fill_gholes_gmctxt_nHole [simp]:
  "C \<noteq> GMHole \<Longrightarrow> num_gholes C = length Ds \<Longrightarrow> fill_gholes_gmctxt C Ds \<noteq> GMHole"
  using fill_gholes_gmctxt.elims by blast

lemma num_gholes_fill_gholes_gmctxt [simp]:
  assumes "num_gholes C = length Ds"
  shows "num_gholes (fill_gholes_gmctxt C Ds) = sum_list (map num_gholes Ds)" using assms
proof (induct C arbitrary: Ds)
  case GMHole then show ?case
    by (cases Ds) simp_all
next
  case (GMFun f Cs)
  then have *: "map (num_gholes \<circ> (\<lambda>i. fill_gholes_gmctxt (Cs ! i) (partition_gholes Ds Cs ! i))) [0..<length Cs] =
    map (\<lambda>i. sum_list (map num_gholes (partition_gholes Ds Cs ! i))) [0 ..< length Cs]"
    and "sum_list (map num_gholes Cs) = length Ds"
    by (auto simp add: length_partition_by_nth)
  then show ?case
    using map_upt_len_conv [of "\<lambda>x. sum_list (map num_gholes x)" "partition_gholes Ds Cs"]
    unfolding partition_holes_fill_holes_mctxt_conv by (simp add: *)
qed

lemma num_gholes_greater0_fill_gholes_gmctxt [intro!]:
  assumes "num_gholes C = length Ds"
    and "\<exists> D \<in> set Ds. 0 < num_gholes D"
  shows "0 < sum_list (map num_gholes Ds)"
  using assms gr_zeroI by force

lemma fill_gholes_gmctxt_fill_gholes:
  assumes len_ds: "length Ds = num_gholes C"
    and nh: "num_gholes (fill_gholes_gmctxt C Ds) = length ss"
  shows "fill_gholes (fill_gholes_gmctxt C Ds) ss =
  fill_gholes C [fill_gholes (Ds ! i) (partition_gholes ss Ds ! i). i \<leftarrow> [0 ..< num_gholes C]]"
  using assms(1)[symmetric] assms(2)
proof (induct C Ds arbitrary: ss rule: fill_gholes_induct)
  case (GMFun f Cs ds ss)
  define qs where "qs = map (\<lambda>i. fill_gholes_gmctxt (Cs ! i) (partition_gholes ds Cs ! i)) [0..<length Cs]"
  then have qs: "\<And>i. i < length Cs \<Longrightarrow> fill_gholes_gmctxt (Cs ! i) (partition_gholes ds Cs ! i) = qs ! i"
    "length qs = length Cs" by auto
  define zs where "zs = map (\<lambda>i. fill_gholes (ds ! i) (partition_gholes ss ds ! i)) [0..<length ds]"
  {fix i assume i: "i < length Cs"
    from GMFun(1) have *: "map length (partition_gholes ds Cs) = map num_gholes Cs" by auto
    have **: "length ss = sum_list (map sum_list (partition_gholes (map num_gholes ds) Cs))"
      using GMFun(1) GMFun(3)[symmetric] num_gholes_fill_gholes_gmctxt[of "GMFun f Cs" ds]
      by (auto simp: comp_def map_map_partition_by[symmetric])
    have "partition_by (partition_by ss
        (map (\<lambda>i. num_gholes (fill_gholes_gmctxt (Cs ! i) (partition_gholes ds Cs ! i))) [0..<length Cs]) ! i)
        (partition_gholes (map num_gholes ds) Cs ! i) = partition_gholes (partition_gholes ss ds) Cs ! i"
      using i GMFun(1) GMFun(3) partition_by_partition_by[OF **]
      by (auto simp: comp_def num_gholes_fill_gholes_gmctxt length_partition_by_nth
        intro!: arg_cong[of _ _ "\<lambda>x. partition_by (partition_by ss x ! _) _"] nth_equalityI)
    then have "map (\<lambda>j. fill_gholes (partition_gholes ds Cs ! i ! j)
        (partition_gholes (partition_gholes ss qs ! i)
        (partition_gholes ds Cs ! i) ! j)) [0..<num_gholes (Cs ! i)] =
        partition_gholes zs Cs ! i" using GMFun(1,3)
      by (auto simp: length_partition_by_nth zs_def qs_def i comp_def partition_by_nth_nth intro: nth_equalityI)}
  then show ?case using GMFun
    by (simp add: qs_def [symmetric] qs zs_def [symmetric] length_partition_by_nth)
qed auto

lemma fill_gholes_gmctxt_sound:
  assumes len_ds: "length Ds = num_gholes C"
  and len_sss: "length sss = num_gholes C"
  and len_ts: "length ts = num_gholes C"
  and insts: "\<And> i. i < length Ds \<Longrightarrow> ts ! i =\<^sub>G\<^sub>f (Ds ! i, sss ! i)"
  shows "fill_gholes C ts =\<^sub>G\<^sub>f (fill_gholes_gmctxt C Ds, concat sss)"
proof (rule eqfI)
  note l_nh_i = eqgfE(2)[OF insts]
  from len_ds len_sss have concat_sss: "partition_gholes (concat sss) Ds = sss"
    by (metis l_nh_i length_map map_nth_eq_conv partition_by_concat_id)
  then show nh: "num_gholes (fill_gholes_gmctxt C Ds) = length (concat sss)"
    unfolding num_gholes_fill_gholes_gmctxt [OF len_ds [symmetric]] length_concat
    by (metis l_nh_i len_ds len_sss nth_map_conv)
  have ts: "ts = [fill_gholes (Ds ! i) (partition_gholes (concat sss) Ds ! i) . i \<leftarrow> [0..<num_gholes C]]" (is "_ = ?fhs")
  proof (rule nth_equalityI)
    show l_fhs: "length ts = length ?fhs" unfolding length_map
      by (metis diff_zero len_ts length_upt)
    fix i
    assume i: "i < length ts"
    then have i': "i < length [0..<num_gholes C]" 
      by (metis diff_zero len_ts length_upt)
    show "ts!i = ?fhs ! i"
      unfolding nth_map[OF i']
      using eqgfE(1)[OF insts[unfolded len_ds, OF i[unfolded len_ts]]] 
      by (metis concat_sss i' len_ds len_sss map_nth nth_map)
  qed
  note ts = this
  show "fill_gholes C ts = fill_gholes (fill_gholes_gmctxt C Ds) (concat sss)"
    unfolding fill_gholes_gmctxt_fill_gholes[OF len_ds nh] ts ..
qed

subsubsection \<open>Semilattice Structures\<close>

lemma inf_gmctxt_idem [simp]:
  "(C :: 'f gmctxt) \<sqinter> C = C"
  by (induct C) (auto simp: zip_same_conv_map intro: map_idI)

lemma inf_gmctxt_GMHole2 [simp]:
  "C \<sqinter> GMHole = GMHole"
  by (induct C) simp_all

lemma inf_gmctxt_comm [ac_simps]:
  "(C :: 'f gmctxt) \<sqinter> D = D \<sqinter> C"
  by (induct C D rule: inf_gmctxt.induct) (fastforce simp: in_set_conv_nth intro!: nth_equalityI)+

lemma inf_gmctxt_assoc [ac_simps]:
  fixes C :: "'f gmctxt"
  shows "C \<sqinter> D \<sqinter> E = C \<sqinter> (D \<sqinter> E)"
  apply (induct C D arbitrary: E rule: inf_gmctxt.induct)
  apply (auto)
  apply (case_tac E, auto)+
  apply (fastforce simp: in_set_conv_nth intro!: nth_equalityI)
  apply (case_tac E, auto)+
done

instantiation gmctxt :: (type) order
begin

definition "(C :: 'a gmctxt) \<le> D \<longleftrightarrow> C \<sqinter> D = C"
definition "(C :: 'a gmctxt) < D \<longleftrightarrow> C \<le> D \<and> \<not> D \<le> C"

instance
  by (standard, simp_all add: less_eq_gmctxt_def less_gmctxt_def ac_simps, metis inf_gmctxt_assoc)

end

lemma less_eq_gmctxt_prime: "C \<le> D \<longleftrightarrow> less_eq_gmctxt C D"
proof
  assume "less_eq_gmctxt C D" then show "C \<le> D"
    by (induct C D rule: less_eq_gmctxt.induct) (auto simp: less_eq_gmctxt_def intro: nth_equalityI)
next
  assume "C \<le> D" then show "less_eq_gmctxt C D" unfolding less_eq_gmctxt_def
  by (induct C D rule: inf_gmctxt.induct)
     (auto split: if_splits simp: set_zip intro!: less_eq_gmctxt.intros nth_equalityI elim!: nth_equalityE, metis)
qed

lemmas less_eq_gmctxt_induct = less_eq_gmctxt.induct[folded less_eq_gmctxt_prime, consumes 1]
lemmas less_eq_gmctxt_intros = less_eq_gmctxt.intros[folded less_eq_gmctxt_prime]

lemma  less_eq_gmctxt_Hole:
  "less_eq_gmctxt C GMHole \<Longrightarrow> C = GMHole"
  using less_eq_gmctxt.cases by blast

lemma num_gholes_at_least1:
  "0 < num_gholes C \<Longrightarrow> 0 < num_gholes (C \<sqinter> D)"
proof (induct C arbitrary: D)
  case (GMFun f Cs)
  from GMFun(2) obtain i where wit: "i < length Cs" "0 < num_gholes (Cs ! i)"
    by (auto, metis (mono_tags, lifting) in_set_conv_nth length_map map_nth_eq_conv not_less sum_list_nonpos)
  note IS = GMFun(1)[OF nth_mem, OF wit]
  show ?case
  proof (cases D)
    case [simp]: (GMFun g Ds)
    {assume "f = g" "length Cs = length Ds"
      then have "0 < num_gholes (Cs ! i \<sqinter> Ds ! i)" using IS[of "Ds ! i"]
        by auto}
    then show ?thesis using wit(1)
      by (auto simp:  split!: prod.splits)
         (smt (verit, del_insts) length_map length_zip map_nth_eq_conv min_less_iff_conj not_gr0 nth_mem nth_zip o_apply prod.simps(2) sum_list_eq_0_iff) 
  qed auto
qed auto

text \<open>
  @{const sup} is defined on compatible multihole contexts.
  Note that compatibility is not transitive.
\<close>
instance gmctxt :: (type) semilattice_inf
  apply (standard)
  apply (auto simp: less_eq_gmctxt_def inf_gmctxt_assoc [symmetric])
  apply (metis inf_gmctxt_comm inf_gmctxt_assoc inf_gmctxt_idem)+
  done


lemma sup_gmctxt_idem [simp]:
  fixes C :: "'f gmctxt"
  shows "C \<squnion> C = C"
  by (induct C) (auto simp: zip_same_conv_map intro: map_idI)

lemma sup_gmctxt_MHole [simp]: "C \<squnion> GMHole = C"
  by (induct C) simp_all

lemma sup_gmctxt_comm [ac_simps]:
  fixes C :: "'f gmctxt"
  shows "C \<squnion> D = D \<squnion> C"
  by (induct C D rule: sup_gmctxt.induct) (fastforce simp: in_set_conv_nth intro!: nth_equalityI)+


lemma comp_gmctxt_refl:
  "(C, C) \<in> comp_gmctxt"
  by (induct C) auto

lemma comp_gmctxt_sym:
  assumes "(C, D) \<in> comp_gmctxt"
  shows "(D, C) \<in> comp_gmctxt"
  using assms by (induct) auto

lemma sup_gmctxt_assoc [ac_simps]:
  assumes "(C, D) \<in> comp_gmctxt" and "(D, E) \<in> comp_gmctxt"
  shows "C \<squnion> D \<squnion> E = C \<squnion> (D \<squnion> E)"
  using assms by (induct C D arbitrary: E) (auto elim!: comp_gmctxt.cases intro!: nth_equalityI)

text \<open>
  No instantiation to @{class semilattice_sup} possible, since @{const sup} is only
  partially defined on terms (e.g., it is not associative in general).
\<close>

interpretation gmctxt_order_bot: order_bot GMHole "(\<le>)" "(<)"
  by (standard) (simp add: less_eq_gmctxt_def)

lemma sup_gmctxt_ge1 [simp]:
  assumes "(C, D) \<in> comp_gmctxt"
  shows "C \<le> C \<squnion> D"
  using assms by (induct C D) (auto simp: less_eq_gmctxt_def intro: nth_equalityI)

lemma sup_gmctxt_ge2 [simp]:
  assumes "(C, D) \<in> comp_gmctxt"
  shows "D \<le> C \<squnion> D"
  using assms by (induct) (auto simp: less_eq_gmctxt_def intro: nth_equalityI)

lemma sup_gmctxt_least:
  assumes "(D, E) \<in> comp_gmctxt"
    and "D \<le> C" and "E \<le> C"
  shows "D \<squnion> E \<le> C"
  using assms
  apply (induct arbitrary: C)
  apply (auto simp: less_eq_gmctxt_def elim!: inf_gmctxt.elims intro!: nth_equalityI)
  apply (metis (erased, lifting) length_map nth_map nth_zip split_conv)
  apply (case_tac "fb = gb \<and> length Csb = length Dsb", simp_all)+
  done

lemma sup_gmctxt_args_MHole2 [simp]:
  "sup_gmctxt_args C GMHole = replicate (num_gholes C) GMHole"
  by (cases C) simp_all

lemma num_gholes_sup_gmctxt_args:
  assumes "(C, D) \<in> comp_gmctxt"
  shows "num_gholes C = length (sup_gmctxt_args C D)"
  using assms by (induct) (auto simp: length_concat intro!: arg_cong [of _ _ sum_list] nth_equalityI)

lemma sup_gmctxt_sup_gmctxt_args:
  assumes "(C, D) \<in> comp_gmctxt"
  shows "fill_gholes_gmctxt C (sup_gmctxt_args C D) = C \<squnion> D" using assms
proof (induct)
  note fill_gholes_gmctxt.simps [simp del]
  case (GMFun f g Cs Ds)
  then show ?case
  proof (cases "f = g \<and> length Cs = length Ds")
    case True
    with GMFun have "\<forall>i < length Cs.
      fill_gholes_gmctxt (Cs ! i) (sup_gmctxt_args (Cs ! i) (Ds ! i)) = Cs ! i \<squnion> Ds ! i"
      and *: "\<forall>i < length Cs. (Cs ! i, Ds ! i) \<in> comp_gmctxt" by (force simp: set_zip)+
    moreover have "partition_gholes (concat (map (case_prod sup_gmctxt_args) (zip Cs Ds)))
      Cs = map (case_prod sup_gmctxt_args) (zip Cs Ds)"
      using True and * by (intro partition_by_concat_id) (auto simp: num_gholes_sup_gmctxt_args)
    ultimately show ?thesis
      using * and True by (auto simp: partition_holes_fill_gholes_gmctxt_conv intro!: nth_equalityI)
  qed auto
qed auto

lemma eqgf_comp_gmctxt:
  assumes "s =\<^sub>G\<^sub>f (C, ss)" and "s =\<^sub>G\<^sub>f (D, ts)"
  shows "(C, D) \<in> comp_gmctxt" using assms
proof (induct s arbitrary: C D ss ts)
  case (GFun f ss C D us vs)
  { fix Cs and Ds
    assume *: "C = GMFun f Cs" "D = GMFun f Ds" and **: "length Cs = length Ds"
    have ?case
    proof (unfold *, intro comp_gmctxt.GMFun [OF refl **] allI impI)
      fix i
      assume "i < length Ds" then show "(Cs ! i, Ds ! i) \<in> comp_gmctxt"
        using GFun by (auto simp: * ** elim!: eqgf_GMFunE) (metis nth_mem)
    qed}
  from GFun.prems this show ?case
  by (cases C D rule: gmctxt.exhaust [case_product gmctxt.exhaust])
    (auto simp: eq_gfill.simps dest: map_eq_imp_length_eq)
qed

lemma eqgf_less_eq [simp]:
  assumes "s =\<^sub>G\<^sub>f (C, ss)"
  shows "C \<le> gmctxt_of_gterm s" using assms
  by (induct rule: eq_gfill_induct) (auto simp: less_eq_gmctxt_prime)

lemma less_eq_comp_gmctxt [simp]:
  "C \<le> D \<Longrightarrow> (C, D) \<in> comp_gmctxt"
  by (induct rule: less_eq_gmctxt_induct) auto

lemma gmctxt_less_eq_sup:
  "(C :: 'f gmctxt) \<le> D \<Longrightarrow> C \<squnion> D = D"
  by (induct rule: less_eq_gmctxt_induct) (auto intro: nth_equalityI)

lemma fill_gholes_gmctxt_less_eq:
  assumes "num_gholes C = length Ds"
  shows "C \<le> fill_gholes_gmctxt C Ds" using assms
proof (induct C arbitrary: Ds)
  case (GMFun f Cs)
  show ?case using GMFun(1)[OF nth_mem] GMFun(2)
    unfolding partition_holes_fill_gholes_gmctxt_conv'
    by (intro less_eq_gmctxt_intros) (auto simp: length_partition_by_nth)
qed simp


lemma less_eq_to_sup_mctxt_args [elim]:
  assumes "C \<le> D"
  obtains Ds where "num_gholes C = length Ds" "D = fill_gholes_gmctxt C Ds"
  using assms gmctxt_less_eq_sup[OF assms]
  using sup_gmctxt_sup_gmctxt_args[OF less_eq_comp_gmctxt[OF assms]]
  using less_eq_comp_gmctxt num_gholes_sup_gmctxt_args
  by force
  
lemma fill_gholes_gmctxt_sup_mctxt_args [simp]:
  assumes "num_gholes C = length Ds"
  shows "sup_gmctxt_args C (fill_gholes_gmctxt C Ds) = Ds" using assms
proof (induct C arbitrary: Ds)
  case GMHole then show ?case
    by (cases Ds) auto
next
  case (GMFun f Cs)
  have "map2 sup_gmctxt_args Cs (map2 fill_gholes_gmctxt Cs (partition_gholes Ds Cs)) = partition_gholes Ds Cs"
    using GMFun(1)[OF nth_mem] GMFun(2)
    by (auto simp: length_partition_by_nth intro!: nth_equalityI)
  then show ?case using GMFun(1)[OF nth_mem] GMFun(2)
    unfolding partition_holes_fill_gholes_gmctxt_conv'
    using concat_partition_by[of "map num_gholes Cs" Ds]
    by auto
qed

lemma map2_fill_gholes_gmctxt_id [simp]:
  assumes "\<And> i. i < length Ds \<Longrightarrow> num_gholes (Ds ! i) = 0"
  shows "map2 fill_gholes_gmctxt Ds (replicate (length Ds) []) = Ds"
  using assms fill_gholes_gmctxt_no_holes[of "Ds ! i" for i]
  by (auto simp: map_nth_eq_conv)

lemma fill_gholes_gmctxt_GMFun_replicate_append [simp]:
  assumes "length Cs = n" and "\<And> t. t \<in> set Ds \<Longrightarrow> num_gholes t = 0"
  shows "fill_gholes_gmctxt (GMFun f ((replicate n GMHole) @ Ds)) Cs = GMFun f (Cs @ Ds)" using assms
proof (induct n arbitrary: Cs)
  case 0 note [simp] = 0(1)
  have "i < length Ds \<Longrightarrow> num_gholes (Ds ! i) = 0" for i using 0 by fastforce
  then show ?case using 0 unfolding partition_holes_fill_gholes_gmctxt_conv'
    by (cases Cs) auto
next
  case (Suc n) then show ?case unfolding partition_holes_fill_gholes_gmctxt_conv'
    by (simp add: Cons_nth_drop_Suc take_Suc_conv_app_nth)
qed

lemma finite_ghole_poss:
  "finite (ghole_poss C)"
  by (induct C) auto

lemma ghole_poss_simp [simp]:
  "ghole_poss (GMFun f cs) = {i # p | i p. i < length cs \<and> p \<in> ghole_poss (cs ! i)}" by auto
declare ghole_poss.simps(2)[simp del]

lemma num_gholes_zero_ghole_poss:
  "num_gholes D = 0 \<Longrightarrow> ghole_poss D = {}"
  by (induct D) auto

lemma ghole_poss_num_gholes_zero:
  "ghole_poss D = {} \<Longrightarrow> num_gholes D = 0"
proof (induct D)
  case (GMFun f Ds)
  then show ?case
    by (simp, metis Collect_empty_eq Collect_mem_eq in_set_idx)
qed simp

lemma num_ghloes_nzero_ghole_poss_nempty:
  "num_gholes D \<noteq> 0 \<Longrightarrow> ghole_poss D \<noteq> {}"
  by (induct D) (auto simp: in_set_conv_nth, fastforce)

lemma ghole_poss_epsE [elim]:
  "ghole_poss D = {[]} \<Longrightarrow> D = GMHole"
  by (induct D) auto

lemma ghole_poss_gmctxt_of_gterm [simp]:
  "ghole_poss (gmctxt_of_gterm t) = {}"
  by (induct t) auto

lemma ghole_poss_subseteq_args [simp]:
  assumes "ghole_poss (GMFun f Ds) \<subseteq> ghole_poss (GMFun g Cs)"
  shows "\<forall> i < min (length Ds) (length Cs). ghole_poss (Ds ! i) \<subseteq> ghole_poss (Cs ! i)" using assms
  by auto

lemma factor_ghole_pos_by_prefix:
  assumes "C \<le> D" "p \<in> ghole_poss D"
  obtains q where "q \<le>\<^sub>p p" "q \<in> ghole_poss C"
  using assms
  by (induct C D arbitrary: p thesis rule: less_eq_gmctxt_induct)
     (auto, metis position_less_eq_Cons)

lemma prefix_and_fewer_gholes_implies_equal_gmctxt:
  "C \<le> D \<Longrightarrow> ghole_poss C \<subseteq> ghole_poss D \<Longrightarrow> C = D"
proof (induct C D rule: less_eq_gmctxt_induct)
  case (1 D) then show ?case by (cases D) auto
next
  case (2 Cs Ds f)
  have "i < length Ds \<Longrightarrow> ghole_poss (Cs ! i) \<subseteq> ghole_poss (Ds ! i)" for i using 2(1,4) by auto
  then show ?case using 2 by (auto intro!: nth_equalityI)
qed

lemma set_sup_gmctxt_args_split:
  "length Cs = length Ds \<Longrightarrow> set (sup_gmctxt_args (GMFun f Cs) (GMFun f Ds)) =
     (\<Union> i \<in> {0..< length Ds}. set (sup_gmctxt_args (Cs ! i) (Ds ! i)))"
  by (auto simp: atLeast0LessThan in_set_zip)
    (metis length_map map_fst_zip nth_mem nth_zip)

lemma gmctxt_closing_trans:
  "gmctxt_closing C D \<Longrightarrow> gmctxt_closing D E \<Longrightarrow> gmctxt_closing C E"
  unfolding gmctxt_closing_def using less_eq_gmctxt_prime
  by (metis (full_types) order_trans)

lemma gmctxt_closing_sup_args_ghole_or_gterm:
  assumes "gmctxt_closing C D"
  shows "\<forall> E \<in> set (sup_gmctxt_args C D). E = GMHole \<or> num_gholes E = 0"
  using assms unfolding gmctxt_closing_def
proof -
  from assms have "C \<le> D" "ghole_poss D \<subseteq> ghole_poss C" unfolding gmctxt_closing_def
    by (auto simp: less_eq_gmctxt_prime)
  then show ?thesis
  proof (induct rule: less_eq_gmctxt_induct)
    case (1 D)
    then show ?case
      by (cases D) (auto simp: in_set_conv_nth intro!: ghole_poss_num_gholes_zero, blast)
  next
    case (2 cs ds f) note IS = this
    show ?case using IS set_sup_gmctxt_args_split[OF IS(1)]
      by auto
  qed
qed

lemma inv_imples_ghole_poss_subseteq:
  "C \<le> D \<Longrightarrow> \<forall> E \<in> set (sup_gmctxt_args C D). E = GMHole \<or> num_gholes E = 0 \<Longrightarrow> ghole_poss D \<subseteq> ghole_poss C"
proof (induct rule: less_eq_gmctxt_induct)
  case (1 D) then show ?case
    by (cases D) (auto simp: num_gholes_zero_ghole_poss)
next
  case (2 cs ds f)
  then show ?case using set_sup_gmctxt_args_split[OF 2(1)]
    by auto (metis (no_types, lifting) fst_conv in_set_zip snd_conv subsetD)
qed

lemma fill_gholes_gmctxt_ghole_poss_subseteq:
  assumes "num_gholes C = length Ds" "\<forall> i < length Ds. Ds ! i = GMHole \<or> num_gholes (Ds ! i) = 0"
  shows "ghole_poss (fill_gholes_gmctxt C Ds) \<subseteq> ghole_poss C" using assms
proof (induct rule: fill_gholes_induct)
  case (GMFun f Cs xs)
  then show ?case unfolding partition_holes_fill_gholes_gmctxt_conv'
    by auto (metis (no_types, lifting) length_map length_partition_by_nth partition_by_nth_nth(1, 2) subsetD)
qed (auto simp: num_gholes_zero_ghole_poss)

lemma ghole_poss_not_in_poss_gmctxt:
  assumes "p \<in> ghole_poss C"
  shows "p \<notin> poss_gmctxt C" using assms
  by (induct C arbitrary: p) auto

lemma comp_gmctxt_inf_ghole_poss_cases:
  assumes "(C, D) \<in> comp_gmctxt" "p \<in> ghole_poss (C \<sqinter> D)"
  shows "p \<in> ghole_poss C \<and> p \<in> ghole_poss D \<or>
    p \<in> ghole_poss C \<and> p \<in> poss_gmctxt D \<or>
    p \<in> ghole_poss D \<and> p \<in> poss_gmctxt C" using assms
proof (induct arbitrary: p)
  case (GMHole1 D) then show ?case
    by (cases D) auto
next
  case (GMHole2 C) then show ?case
    by (cases C) auto
next
  case (GMFun f g Cs Ds)
  then show ?case
    by (auto simp: atLeast0LessThan) blast+
qed

lemma length_ghole_poss_list_num_gholes:
  "num_gholes C = length (ghole_poss_list C)"
  by (induct C) (auto simp: length_concat intro: nth_sum_listI)

lemma ghole_poss_list_distict:
  "distinct (ghole_poss_list C)"
proof (induct C)
  case (GMFun f Cs)
  then show ?case proof (induct Cs rule: rev_induct)
    case (snoc x xs)
    then have "distinct (ghole_poss_list (GMFun f xs))" "distinct (ghole_poss_list x)" by auto
    then show ?case using snoc by (auto simp add: map_cons_presv_distinct dest: set_zip_leftD)
  qed auto
qed auto

lemma ghole_poss_ghole_poss_list_conv:
  "ghole_poss C = set (ghole_poss_list C)"
proof (induct C)
  case (GMFun f Cs) note IS = GMFun[OF nth_mem]
  {fix p assume "p \<in> ghole_poss (GMFun f Cs)"
    then obtain i ps where w: "p = i # ps" "i < length Cs"
      "ps \<in> ghole_poss (Cs ! i)" by auto
    then have "(i, Cs ! i) \<in> set (zip [0..<length Cs] Cs)"
      by (force simp: in_set_zip)
    then have "p \<in> set (ghole_poss_list (GMFun f Cs))" using IS[of i] w
      by auto}
  then show ?case using IS
    by (auto simp: in_set_zip)
qed auto

lemma card_ghole_poss_num_gholes:
  "card (ghole_poss C) = num_gholes C"
  unfolding ghole_poss_ghole_poss_list_conv
  unfolding length_ghole_poss_list_num_gholes
  using ghole_poss_list_distict
  using distinct_card by blast

lemma subgm_at_hole_poss [simp]:
  "p \<in> ghole_poss C \<Longrightarrow> subgm_at C p = GMHole"
  by (induct C arbitrary: p) auto

lemma subgm_at_mctxt_of_term:
  "p \<in> gposs t \<Longrightarrow> subgm_at (gmctxt_of_gterm t) p = gmctxt_of_gterm (gsubt_at t p)"
  by (induct t arbitrary: p) auto

lemma num_gholes_subgm_at:
  assumes "p \<in> poss_gmctxt C"
  shows "num_gholes (subgm_at C p) = ghole_num_at_pos p C" using assms
  by (induct C arbitrary: p) auto

lemma gmctxt_subtgm_at_fill_args_empty_pos [simp]:
  assumes "num_gholes C = length ts"
  shows "gmctxt_subtgm_at_fill_args [] C ts = ts"
  using assms by (auto simp: gmctxt_subtgm_at_fill_args_def)

lemma ghole_num_bef_at_pos_num_gholes_less_eq:
  assumes "p \<in> poss_gmctxt C"
  shows "ghole_num_bef_pos p C + ghole_num_at_pos p C \<le> num_gholes C" using assms
proof (induct C arbitrary: p)
  case (GMFun f Cs)
  show ?case 
  proof (cases p)
    case (Cons i ps)
    have *: "num_gholes (GMFun f Cs) = sum_list (map num_gholes (take i Cs)) + num_gholes (Cs ! i) + sum_list (map num_gholes (drop (Suc i) Cs))"
      using GMFun(2) unfolding Cons
      by (auto simp flip: take_map take_drop)
         (metis Cons_nth_drop_Suc add.assoc append_take_drop_id drop_map length_map nth_map sum_list.Cons sum_list.append)
    from Cons have
      "(sum_list (map num_gholes (take i Cs)) + (ghole_num_bef_pos ps (Cs ! i) + ghole_num_at_pos ps (Cs ! i)))
       + sum_list (map num_gholes (drop (Suc i) Cs)) \<le>
       (sum_list (map num_gholes (take i Cs)) + num_gholes (Cs ! i)) + sum_list (map num_gholes (drop (Suc i) Cs))"
      using GMFun(1)[OF nth_mem, of i ps] GMFun(2)
      by auto
    from add_le_imp_le_right[OF this] show ?thesis using GMFun(2) *
      unfolding Cons
      by simp
  qed auto
qed auto

lemma ghole_num_at_pos_fill_args_length:
  assumes "p \<in> poss_gmctxt C" "num_gholes C = length ts"
  shows "ghole_num_at_pos p C = length (gmctxt_subtgm_at_fill_args p C ts)"
  using ghole_num_bef_at_pos_num_gholes_less_eq[OF assms(1)] assms(2)
  by (auto simp: gmctxt_subtgm_at_fill_args_def)

lemma ghole_poss_nth_subt_at:
  assumes "t =\<^sub>G\<^sub>f (C, ts)" and "p \<in> ghole_poss C"
  shows "ghole_num_bef_pos p C < length ts \<and> gsubt_at t p = ts ! ghole_num_bef_pos p C" using assms
proof (induct arbitrary: p rule: eq_gfill_induct)
  case (GMFun f ss Cs ts)
  let ?ts = "partition_gholes ts Cs"
  from GMFun obtain i and q where [simp]: "p = i # q"
    and "i < length ss" and "q \<in> ghole_poss (Cs ! i)" by auto
  with GMFun.hyps have "ss ! i =\<^sub>G\<^sub>f (Cs ! i, ?ts ! i)"
    and j: "ghole_num_bef_pos q (Cs ! i) < length (?ts ! i)" (is "?j < length _")
    and *: "?ts ! i ! ghole_num_bef_pos q (Cs ! i) = gsubt_at (ss ! i) q"
    by auto
  let ?k = "sum_list (map length (take i ?ts)) + ?j"
  have "i < length ?ts" using \<open>i < length ss\<close> and GMFun by auto
  with partition_by_nth_nth_old [OF this j] and GMFun and concat_nth_length [OF this j]
    have "?ts ! i ! ?j = ts ! ?k" and "?k < length ts" by (auto)
  moreover with * have "ts ! ?k = gsubt_at (GFun f ss) p" using \<open>i < length ss\<close> by simp
  ultimately show ?case using GMFun.hyps(2) by (auto simp: take_map [symmetric])
qed auto

lemma poss_gmctxt_fill_gholes_split:
  assumes "t =\<^sub>G\<^sub>f (C, ts)" and "p \<in> poss_gmctxt C"
  shows "gsubt_at t p =\<^sub>G\<^sub>f (subgm_at C p , gmctxt_subtgm_at_fill_args p C ts)"
  using assms
proof (induct arbitrary: p rule: eq_gfill_induct)
  case (GMFun f ss Cs ts)
  let ?ts = "partition_gholes ts Cs"
  from GMFun have "\<And> i. i < length Cs \<Longrightarrow> ss ! i =\<^sub>G\<^sub>f (Cs ! i, ?ts ! i)" by auto
  show ?case
  proof (cases p)
    case Nil
    then have "GFun f ss =\<^sub>G\<^sub>f (GMFun f Cs, concat ?ts)" using GMFun
      by (intro eqgf_GMFunI) (auto simp del: fill_gholes.simps)
    then show ?thesis using GMFun unfolding Nil
      by simp
  next
    case (Cons i q)
    then have "ghole_num_at_pos q (Cs ! i) \<le> num_gholes (Cs ! i) - ghole_num_bef_pos q (Cs ! i)"
      using GMFun(1, 2, 4) ghole_num_bef_at_pos_num_gholes_less_eq[of q "Cs ! i"]
      by auto
    then show ?thesis using GMFun
      by (auto simp: Cons add.commute gmctxt_subtgm_at_fill_args_def partition_by_nth drop_take take_map min_def split!: if_splits)
  qed
qed auto

lemma fill_gholes_ghole_poss:
  assumes "t =\<^sub>G\<^sub>f (C, ts)" and "i < length ts"
  shows "gsubt_at t (ghole_poss_list C ! i) = ts ! i" using assms
proof (induct arbitrary: i rule: eq_gfill_induct)
  case (GMFun f ss Cs ts)
  have *: "length (concat (poss_rec ghole_poss_list Cs)) = num_gholes (GMFun f Cs)"
    using GMFun(1, 2, 4)
    unfolding length_ghole_poss_list_num_gholes[of "GMFun f Cs", symmetric, unfolded ghole_poss_list.simps]
    by auto
  from GMFun have b: "i < length (concat (partition_gholes ts Cs))" by simp
  then have ts: "ts ! i = (\<lambda> (j, k). partition_gholes ts Cs ! j ! k) (concat_index_split (0, i) (partition_gholes ts Cs))"
    by (metis GMFun.hyps(2) concat_index_split_sound concat_partition_by)
  obtain o_idx i_idx where csp: "concat_index_split (0, i) (partition_gholes ts Cs) = (o_idx, i_idx)"
    using old.prod.exhaust by blast
  have idx: "o_idx < length Cs" "i_idx < length (partition_gholes ts Cs ! o_idx)"
    using concat_index_split_sound_bounds[OF b csp] by auto
  have "concat_index_split (0, i) (poss_rec ghole_poss_list Cs) = (o_idx, i_idx)"
    using GMFun(1, 2, 4) * unfolding csp[symmetric]
    by (intro concat_index_split_unique, unfold *)
       (auto, simp add: length_ghole_poss_list_num_gholes length_partition_gholes_nth)
  then have gp: "ghole_poss_list (GMFun f Cs) ! i = poss_rec ghole_poss_list Cs ! o_idx ! i_idx"
    by (simp add: "*" GMFun.hyps(2) GMFun.prems concat_index_split_less_length_concat(4))
  from idx GMFun have r: "o_idx < length (zip [0..<length ss] Cs)" by auto
  then show ?case using GMFun idx unfolding ts csp gp
    by (auto simp: nth_map[OF r] length_ghole_poss_list_num_gholes length_partition_gholes_nth split: prod.splits)
qed auto

lemma length_unfill_gholes [simp]:
  assumes "C \<le> gmctxt_of_gterm t"
  shows "length (unfill_gholes C t) = num_gholes C"
  using assms
proof (induct C t rule: unfill_gholes.induct)
  case (2 f Cs g ts) with 2(1)[OF _ nth_mem] 2(2) show ?case
    by (auto simp: less_eq_gmctxt_def length_concat
      intro!: cong[of sum_list, OF refl] nth_equalityI elim!: nth_equalityE)
qed auto

lemma fill_gholes_arbitrary:
  assumes lCs: "length Cs = length ts"
    and lss: "length ss = length ts"
    and rec: "\<And> i. i < length ts \<Longrightarrow> num_gholes (Cs ! i) = length (ss ! i) \<and> f (Cs ! i) (ss ! i) = ts ! i"
  shows "map (\<lambda>i. f (Cs ! i) (partition_gholes (concat ss) Cs ! i)) [0 ..< length Cs] = ts"
proof -
  have "sum_list (map num_gholes Cs) = length (concat ss)" using assms
    by (auto simp: length_concat map_nth_eq_conv intro: arg_cong[of _ _ "sum_list"])
  moreover have "partition_gholes (concat ss) Cs = ss"
    using assms by (auto intro: partition_by_concat_id)
  ultimately show ?thesis using assms by (auto intro: nth_equalityI)
qed

lemma fill_unfill_gholes:
  assumes "C \<le> gmctxt_of_gterm t"
  shows "fill_gholes C (unfill_gholes C t) = t"
  using assms
proof (induct C t rule: unfill_gholes.induct)
  case (2 f Cs g ts) with 2(1)[OF _ nth_mem] 2(2) show ?case
    by (auto simp: less_eq_gmctxt_def unfill_gholes_conv intro!: fill_gholes_arbitrary elim!: nth_equalityE)
qed (auto split: if_splits)

lemma funas_gmctxt_of_mctxt [simp]:
  "ground_mctxt C \<Longrightarrow> funas_gmctxt (gmctxt_of_mctxt C) = funas_mctxt C"
  by (induct C) (auto simp: funas_gterm_gterm_of_term)

lemma funas_mctxt_of_gmctxt_conv:
  "funas_mctxt (mctxt_of_gmctxt C) = funas_gmctxt C"
  by (induct C) (auto simp flip: funas_gterm_gterm_of_term)

lemma funas_gterm_ctxt_apply [simp]:
  assumes "num_gholes C = length ss"
  shows "funas_gterm (fill_gholes C ss) = funas_gmctxt C \<union> \<Union> (set (map funas_gterm ss))" using assms
proof (induct rule: fill_gholes_induct)
  case (GMFun f Cs ss)
  show ?case using GMFun partition_gholes_subseteq[OF GMFun(1)]
    by (auto simp add: Un_Union_image simp del: map_partition_by_nth)
qed simp

lemma funas_gmctxt_gmctxt_of_gterm [simp]:
  "funas_gmctxt (gmctxt_of_gterm s) = funas_gterm s"
  by (induct s) auto

lemma funas_gmctxt_replicate_GMHole [simp]:
  "funas_gmctxt (GMFun f (replicate n GMHole)) = {(f, n)}"
  by auto

lemma funas_gmctxt_gmctxt_of_gctxt [simp]:
  "funas_gmctxt (gmctxt_of_gctxt C) = funas_gctxt C"
  by (induct C) auto

lemma funas_gmctxt_fill_gholes_gmctxt [simp]:
  assumes "num_gholes C = length Ds"
  shows "funas_gmctxt (fill_gholes_gmctxt C Ds) = funas_gmctxt C \<union> \<Union>(set (map funas_gmctxt Ds))"
  (is "?f C Ds = ?g C Ds") using assms
proof (induct C arbitrary: Ds)
  case GMHole then show ?case by (cases Ds) simp_all
next
  case (GMFun f Cs)
  then have num_gholes: "sum_list (map num_gholes Cs) = length Ds" by simp
  let ?ys = "partition_gholes Ds Cs"
  have "\<And>i. i < length Cs \<Longrightarrow> ?f (Cs ! i) (?ys ! i) = ?g (Cs ! i) (?ys ! i)"
    by (simp add: GMFun.hyps length_partition_by_nth num_gholes)
  then have "(\<Union>i \<in> {0 ..< length Cs}. ?f (Cs ! i) (?ys ! i)) =
    (\<Union>i \<in> {0 ..< length Cs}. ?g (Cs ! i) (?ys ! i))" by simp
  then show ?case
    using num_gholes unfolding partition_holes_fill_holes_mctxt_conv
    by (simp add: UN_Un_distrib UN_upt_len_conv [of _ _ "\<lambda>x. \<Union>(set x)"] UN_set_partition_by_map)
qed

lemma funas_supremum:
  "C \<le> D \<Longrightarrow> funas_gmctxt D = funas_gmctxt C \<union> \<Union> (set (map funas_gmctxt (sup_gmctxt_args C D)))"
  using fill_gholes_gmctxt_sup_mctxt_args[of C]
  by (auto simp: fill_gholes_gmctxt_sup_mctxt_args[of C] elim!: less_eq_to_sup_mctxt_args[of C D])

lemma funas_gctxt_gctxt_of_gmctxt [simp]:
  "num_gholes D = Suc 0 \<Longrightarrow> funas_gctxt (gctxt_of_gmctxt D) = funas_gmctxt D"
  by (metis One_nat_def funas_gmctxt_gmctxt_of_gctxt gmctxt_of_gctxt_gctxt_of_gmctxt)

lemma funas_gterm_gterm_of_gmctxt [simp]:
  "num_gholes C = 0 \<Longrightarrow> funas_gterm (gterm_of_gmctxt C) = funas_gmctxt C"
  by (metis funas_gmctxt_gmctxt_of_gterm no_gholes_gmctxt_of_gterm_gterm_of_gmctxt_id)

lemma less_sup_gmctxt_args_funas_gmctxt:
  "C \<le> D \<Longrightarrow> funas_gmctxt C \<subseteq> \<F> \<Longrightarrow> \<forall> Ds \<in> set (sup_gmctxt_args C D). funas_gmctxt Ds \<subseteq> \<F> \<Longrightarrow> funas_gmctxt D \<subseteq> \<F>"
  using funas_supremum[of C D] by auto

lemma funas_gmctxt_poss_gmctxt_subgm_at_funas:
  assumes "funas_gmctxt C \<subseteq> \<F>"  "p \<in> poss_gmctxt C"
  shows "funas_gmctxt (subgm_at C p) \<subseteq> \<F>"
  using assms
proof (induct C arbitrary: p)
  case (GMFun f Cs)
  then show ?case
    by (auto, blast) (metis SUP_le_iff nth_mem subsetD)
qed auto

lemma inf_funas_gmctxt_subset1:
  "funas_gmctxt (C \<sqinter> D) \<subseteq> funas_gmctxt C"
  using funas_supremum[of C "C \<sqinter> D"]
  by (metis funas_supremum inf_le1 le_sup_iff order_refl)

lemma inf_funas_gmctxt_subset2:
  "funas_gmctxt (C \<sqinter> D) \<subseteq> funas_gmctxt D"
  using funas_supremum[of D "C \<sqinter> D"]
  by (metis funas_supremum inf_le2 le_sup_iff order_refl)


end