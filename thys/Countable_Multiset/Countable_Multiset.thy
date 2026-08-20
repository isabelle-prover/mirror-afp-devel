theory Countable_Multiset
  imports
    "HOL-Library.Countable_Set_Type"
    "HOL-Library.Extended_Nat"
    "Coinductive.Coinductive_List"
    "HOL-Library.BNF_Corec"
    Infinite_Sums_Enat
begin

section \<open>Miscellaneous (Mostly About Lazy Lists)\<close>

lemma bij_betw_singl_remap: \<open>bij_betw \<pi> A B \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow>
  bij_betw (\<pi>(inv_into A \<pi> y := \<pi> x)) (A - {x}) (B - {y})\<close>
  by (auto simp: bij_betw_def inj_on_def image_iff)

lemma ldropWhile_eq_LCons_iff: \<open>ldropWhile P lxs = LCons x lxs' \<longleftrightarrow> (\<not> P x \<and>
  (\<exists>xs. lxs = lappend (llist_of xs) (LCons x lxs') \<and> (\<forall>x \<in> set xs. P x)))\<close>
proof -
  have False
    if \<open>ldropWhile P lxs = LCons x lxs'\<close> and \<open>P x\<close>
    using that by (metis lhd_LCons lhd_ldropWhile llist.disc(2) lnull_ldropWhile)
  moreover have \<open>\<exists>xs. lxs = lappend (llist_of xs) (LCons x lxs') \<and> (\<forall>x\<in>set xs. P x)\<close>
    if \<open>ldropWhile P lxs = LCons x lxs'\<close>
    using that by (metis eq_LConsD in_lset_lappend_iff lappend_ltakeWhile_ldropWhile
        ldropWhile_eq_LNil_iff llist_of_list_of lset_llist_of lset_ltakeWhileD)
  ultimately show ?thesis
    by (auto simp: ldropWhile_lappend)
qed

lemma ltakeWhile_ldropWhile_decomp:
  assumes \<open>x \<in> lset lxs\<close>
  shows \<open>lxs = lappend (ltakeWhile ((\<noteq>) x) lxs) (LCons x (ltl (ldropWhile ((\<noteq>) x) lxs)))\<close>
proof (subst lappend_ltakeWhile_ldropWhile[symmetric, of lxs \<open>(\<noteq>) x\<close>], rule arg_cong[where f=\<open>lappend _\<close>])
  from assms show \<open>ldropWhile ((\<noteq>) x) lxs = LCons x (ltl (ldropWhile ((\<noteq>) x) lxs))\<close>
    by (cases \<open>ldropWhile ((\<noteq>) x) lxs\<close>)
      (auto simp: ldropWhile_eq_LNil_iff lhd_ldropWhile[where P=\<open>(\<noteq>) x\<close>, simplified, symmetric]  dest!: eq_LConsD)
qed

lemma lzip_lmap_same: \<open>lzip (lmap f lxs) (lmap g lxs) = lmap (\<lambda>x. (f x, g x)) lxs\<close>
  by (coinduction arbitrary: lxs) auto

lemma llength_not_lnull: \<open>\<not> lnull lxs \<Longrightarrow> llength lxs = eSuc (llength (ltl lxs))\<close>
  by (auto simp: lnull_def neq_LNil_conv)

primrec ltaken :: \<open>nat \<Rightarrow> 'a llist \<Rightarrow> 'a list\<close> where
  \<open>ltaken 0 lxs = []\<close>
| \<open>ltaken (Suc i) lxs = (case lxs of LNil \<Rightarrow> [] | LCons x lxs \<Rightarrow> x # ltaken i lxs)\<close>

lemma nth_ltaken: \<open>m < n \<Longrightarrow> n \<le> llength lxs \<Longrightarrow> nth (ltaken n lxs) m = lnth lxs m\<close>
  by (induct n arbitrary: m lxs) (auto simp: nth_Cons' gr0_conv_Suc simp flip: eSuc_enat split: llist.splits)

lemma set_ltaken: \<open>set (ltaken n lxs) \<subseteq> lset lxs\<close>
  by (induct n arbitrary: lxs) (force split: llist.splits)+

lemma length_ltaken: \<open>length (ltaken n lxs) = (if enat n \<le> llength lxs then n else the_enat (llength lxs))\<close>
  by (induct n arbitrary: lxs)
    (auto simp: enat_0 min_def not_le eSuc_enat enat_0_iff eSuc_enat_iff elim!: less_enatE split: llist.splits)

lemma set_ltaken_conv: \<open>n \<le> llength lxs \<Longrightarrow> set (ltaken n lxs) = lnth lxs ` {0..<n}\<close>
proof (induct n arbitrary: lxs)
  case (Suc n)
  then show ?case
    by (cases lxs)
      (force simp flip: eSuc_enat simp: image_iff lnth_LCons' dest: bspec[of _ _ \<open>Suc _\<close>])+
qed simp

lemma ltaken_lappend:
  \<open>ltaken n (lappend lxs lys) = (case llength lxs of \<infinity> \<Rightarrow> ltaken n lxs | enat m \<Rightarrow> ltaken n lxs @ ltaken (n - m) lys)\<close>
  by (induct n arbitrary: lxs) (auto split: enat.splits simp: enat_0_iff eSuc_enat_iff eSuc_eq_infinity_iff split: llist.splits)

lemma ltaken_LNil[simp]: \<open>ltaken i LNil = []\<close>
  by (cases i) auto


section \<open>enat as a Codatatype\<close>

codatatype en = eZ | eS (ep: en)
  where \<open>ep eZ = eZ\<close>

coinductive is_einf where
  \<open>is_einf n \<Longrightarrow> is_einf (eS n)\<close>

inductive is_fin where
  \<open>is_fin eZ\<close>
| \<open>is_fin n \<Longrightarrow> is_fin (eS n)\<close>

lemma not_is_fin_is_einf: \<open>\<not> is_fin n \<Longrightarrow> is_einf n\<close>
proof (coinduction arbitrary: n)
  case is_einf
  then show ?case
    by (cases n) (auto intro: is_fin.intros)
qed

lemma is_fin_not_is_einf: \<open>is_fin n \<Longrightarrow> \<not> is_einf n\<close>
  by (induct n pred: is_fin) (auto elim: is_einf.cases)

primcorec einf where
  \<open>einf = eS einf\<close>

lemma einf_eS_iff: \<open>einf = eS x \<longleftrightarrow> x = einf\<close>
  by (subst einf.code) auto

lemma is_einf_einf: \<open>is_einf einf\<close>
  by (coinduction; subst einf.code) auto

lemma is_einf_eq_einf: \<open>is_einf n \<Longrightarrow> n = einf\<close>
  by (coinduction arbitrary: n) (auto elim: is_einf.cases)

fun nat_to_en where
  \<open>nat_to_en 0 = eZ\<close>
| \<open>nat_to_en (Suc n) = eS (nat_to_en n)\<close>

lemma is_fin_ex_nat_to_en: \<open>is_fin n \<Longrightarrow> \<exists>m. n = nat_to_en m\<close>
  by (induct n pred: is_fin) (auto intro: exI[of _ 0] exI[of _ \<open>Suc _\<close>])

lemma inj_nat_to_en: \<open>nat_to_en x = nat_to_en y \<Longrightarrow> x = y\<close>
proof (induct x arbitrary: y)
  case 0
  then show ?case
    by (cases y; simp)
next
  case (Suc x)
  then show ?case 
    by (cases y; simp)
qed

lemma nat_to_en_not_einf: \<open>nat_to_en n = einf \<Longrightarrow> False\<close>
  by (induct n; subst (asm) einf.code) auto

definition enat_to_en where
  \<open>enat_to_en n = (case n of enat n \<Rightarrow> nat_to_en n | _ \<Rightarrow> einf)\<close>

lemma inj_enat_to_en: \<open>inj enat_to_en\<close>
  by (auto simp: inj_on_def enat_to_en_def inj_nat_to_en
      intro: nat_to_en_not_einf nat_to_en_not_einf[OF sym] split: enat.splits)

lemma range_enat_to_en: \<open>n \<in> range enat_to_en\<close>
proof (cases \<open>n = einf\<close>)
  case True
  then show ?thesis by (intro image_eqI[of _ _ \<infinity>]) (auto simp: enat_to_en_def)
next
  case False
  then have \<open>is_fin n\<close>
    using is_einf_eq_einf not_is_fin_is_einf by auto
  then obtain m where \<open>n = nat_to_en m\<close>
    using is_fin_ex_nat_to_en by blast
  then show ?thesis
    by (intro image_eqI[of _ _ \<open>enat m\<close>]) (auto simp: enat_to_en_def)
qed

lemma type_definition_enat: \<open>type_definition enat_to_en (inv enat_to_en) UNIV\<close>
  by standard (auto intro: inv_f_f f_inv_into_f inj_enat_to_en simp: range_enat_to_en)

setup_lifting type_definition_enat

lift_definition corec_enat :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> enat) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> enat\<close>
  is corec_en .

lemma eZ_transfer[transfer_rule]: \<open>pcr_enat eZ 0\<close>
  by (auto simp: pcr_enat_def cr_enat_def enat_to_en_def enat_0[symmetric])

lemma eS_transfer[transfer_rule]: \<open>rel_fun pcr_enat pcr_enat eS eSuc\<close>
  by (auto simp: pcr_enat_def cr_enat_def enat_to_en_def rel_fun_def eSuc_enat einf.code[symmetric]
      eq_OO split: enat.splits)

lemma ep_nat_to_en: \<open>ep (nat_to_en n) = nat_to_en (n - Suc 0)\<close>
  by (induct n) (auto)

lemma ep_transfer[transfer_rule]: \<open>rel_fun pcr_enat pcr_enat ep epred\<close>
  by (auto simp: pcr_enat_def cr_enat_def enat_to_en_def rel_fun_def eSuc_enat einf.code[symmetric]
      eq_OO ep_nat_to_en split: enat.splits)

lemma corec_enat_code[code]:
  \<open>corec_enat zer stop end cnt a =
   (if zer a then 0 else eSuc (if stop a then end a else corec_enat zer stop end cnt (cnt a)))\<close>
  by transfer (rule en.corec_code)

instantiation en :: comm_monoid_add
begin

definition zero_en where \<open>zero_en = eZ\<close>

primcorec plus_en where
  \<open>plus_en e1 e2 = (case e1 of eZ \<Rightarrow> e2 | eS e1' \<Rightarrow> eS (plus_en e1' e2))\<close>

friend_of_corec plus :: \<open>en \<Rightarrow> en \<Rightarrow> en\<close> where
  \<open>e1 + e2 = (case e1 of eZ \<Rightarrow> (case e2 of eZ \<Rightarrow> eZ | eS e2' \<Rightarrow> eS e2') | eS e1' \<Rightarrow> eS (e1' + e2))\<close>
  by (subst plus_en.code; simp split: en.splits) transfer_prover

lemma plus_einf_left[simp]: \<open>einf + e = einf\<close>
  by (coinduction arbitrary: e, subst (5) einf.code) (auto split: en.splits)

lemma eZ_left_neutral[simp]: \<open>eZ + e = e\<close>
  by (simp add: plus_en.code)
lemma eZ_right_neutral[simp]: \<open>e + eZ = e\<close>
  by (coinduction arbitrary: e) (auto split: en.splits)
lemma plus_eS_left[simp]: \<open>eS e1 + e2 = eS (e1 + e2)\<close>
  by (simp add: plus_en.code)
lemma plus_eS_right[simp]: \<open>e1 + eS e2 = eS (e1 + e2)\<close>
  by (coinduction arbitrary: e1 e2 rule: en.coinduct_strong) (auto split: en.splits)

instance
proof
  fix n m q :: en
  show \<open>n + m + q = n + (m + q)\<close>
    by (coinduction arbitrary: n m q rule: en.coinduct_strong)
      (force split: en.splits intro: exI[of _ eZ] exI[of _ \<open>eS _\<close>])
  show \<open>n + m = m + n\<close>
    by (coinduction arbitrary: n m rule: en.coinduct_strong)
      (force split: en.splits intro: exI[of _ \<open>eS _\<close>])
  show \<open>0 + n = n\<close>
    by (coinduction arbitrary: n) (auto simp: zero_en_def split: en.splits)
qed

end

lemma plus_einf_right[simp]: \<open>e + einf = einf\<close>
  by (simp add: add.commute)

lemma nat_to_en_plus[simp]: \<open>nat_to_en (m + n) = nat_to_en m + nat_to_en n\<close>
  by (induct m) auto

lemma ezero_transfer[transfer_rule]: \<open>pcr_enat 0 0\<close>
  by (auto simp: zero_en_def eZ_transfer)

lemma eplus_transfer[transfer_rule]: \<open>rel_fun pcr_enat (rel_fun pcr_enat pcr_enat) (+) (+)\<close>
  by (auto simp: pcr_enat_def cr_enat_def enat_to_en_def rel_fun_def eSuc_enat einf.code[symmetric]
      eq_OO ep_nat_to_en split: enat.splits)

lemma case_en_transfer[transfer_rule]: \<open>rel_fun R (rel_fun (rel_fun pcr_enat R) (rel_fun pcr_enat R)) case_en co.case_enat\<close>
  by (auto simp: pcr_enat_def cr_enat_def enat_to_en_def rel_fun_def eSuc_enat einf.code[symmetric]
      eq_OO ep_nat_to_en enat_0_iff enat_eSuc_iff infinity_eq_eSuc_iff einf_eS_iff split: enat.splits en.splits co.enat.splits)

corec lsum_en where
  \<open>lsum_en lxs = (case ldropWhile ((=) 0) lxs of LNil \<Rightarrow> 0 | LCons e lxs \<Rightarrow> eS (ep e + lsum_en lxs))\<close>

lift_definition lsum :: \<open>enat llist \<Rightarrow> enat\<close>
  is lsum_en .

lemmas lsum_code[code] = lsum_en.code[transferred]

lemma lsum_code_alt:
  \<open>lsum lxs = (case ldropWhile ((=) 0) lxs of LNil \<Rightarrow> 0 | LCons e lxs \<Rightarrow> e + lsum lxs)\<close>
  by (subst lsum_code, cases \<open>lhd (ldropWhile ((=) 0) lxs)\<close> rule: co.enat.exhaust)
    (auto simp: iadd_Suc dest: ldropWhile_eq_LCons_iff[THEN iffD1] split: llist.splits)

section \<open>Counting in Lazy Lists\<close>

primcorec count_llist_en where
  \<open>count_llist_en lxs x  = (if x \<in> lset lxs then eS (count_llist_en (ltl (ldropWhile ((\<noteq>) x) lxs)) x) else eZ)\<close>

lift_definition count_llist :: \<open>'a llist \<Rightarrow> 'a \<Rightarrow> enat\<close>
  is count_llist_en .

lemmas count_llist_code[code] = count_llist_en.code[transferred]
lemmas count_llist_sel[simp] = count_llist_en.sel[transferred]
lemmas count_llist_ctr = count_llist_en.ctr[transferred]
lemmas enat_coinduct_strong[case_names eq_enat, coinduct type] = en.coinduct_strong[transferred]

lift_definition enat_cong :: \<open>(enat \<Rightarrow> enat \<Rightarrow> bool) \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> bool\<close> is \<open>en.congclp\<close> .
lemmas enat_coinduct_upto[case_names eq_enat] = en.coinduct_upto[transferred]
lemmas enat_cong_intros = en.cong_intros[transferred]

lifting_update enat.lifting
lifting_forget enat.lifting

lemma in_lset_iff_count_llist: \<open>x \<in> lset lxs \<longleftrightarrow> count_llist lxs x \<noteq> 0\<close>
  by (subst count_llist_code) auto

lemma count_llist_zero_iff:  \<open>count_llist lxs x = 0 \<longleftrightarrow> x \<notin> lset lxs\<close>
  by (metis in_lset_iff_count_llist)

lemma count_llist_alt: \<open>count_llist lxs x = llength (lfilter ((=) x) lxs)\<close>
  by (coinduction arbitrary: lxs) (auto simp: count_llist_zero_iff epred_llength ltl_lfilter)

lemma count_llist_lappend: 
  \<open>count_llist (lappend lxs lys) x = count_llist lxs x + (if lfinite lxs then count_llist lys x else 0)\<close>
proof (coinduction arbitrary: lxs lys)
  case eq_enat
  then show ?case
    by (auto simp: count_llist_zero_iff epred_iadd1 lset_lappend_conv lappend_inf ldropWhile_lappend
        lfinite_ldropWhile count_llist_ctr(1)[of x lxs])
qed

lemma count_llist_LNil[simp]: \<open>count_llist LNil x = 0\<close>
  by (subst count_llist_code) auto

lemma count_llist_LCons[simp]: \<open>count_llist (LCons y lxs) x = 
  (if x = y then eSuc (count_llist lxs x) else count_llist lxs x)\<close>
  by (subst (1 3) count_llist_code) (auto simp: count_llist_zero_iff)

section \<open>Lazy Lists of Natural Numbers\<close>

primcorec lupt where
  \<open>lupt i j = (if enat i \<ge> j then LNil else LCons i (lupt (Suc i) j))\<close>

lemma lset_luptD[OF _ refl]:
  assumes \<open>k \<in> lset lxs\<close> \<open>lxs = lupt i j\<close>
  shows \<open>i \<le> k\<close> \<open>k < j\<close>
  using assms
proof (induct k lxs arbitrary: i rule: llist.set_induct)
  case (LCons1 z1 z2)
  {
    case 1
    then show ?case
      by (subst (asm) lupt.code) (auto split: if_splits)
  next
    case 2
    then show ?case
      by (subst (asm) lupt.code) (auto split: if_splits)
  }
next
  case (LCons2 z1 z2 k)
  {
    case 1
    with LCons2(2,3)[of \<open>Suc i\<close>] show ?case
      by (subst (asm) (3) lupt.code) (auto split: if_splits)
  next
    case 2
    with LCons2(2,3)[of \<open>Suc i\<close>] show ?case
      by (subst (asm) (3) lupt.code) (auto split: if_splits)
  }
qed

lemma lset_luptI: \<open>i \<le> k \<Longrightarrow> enat k < j \<Longrightarrow> k \<in> lset (lupt i j)\<close>
proof (induct \<open>k - i\<close> arbitrary: i)
  case 0
  then show ?case
    by (subst lupt.code) auto
next
  case (Suc x)
  then have \<open>enat i < j\<close>
    by (meson enat_ord_simps(1) order.strict_trans1)
  from Suc(2) have \<open>x = k - Suc i\<close>
    by force
  with Suc(1)[OF this] Suc(2-4) \<open>enat i < j\<close> show ?case
    by (subst lupt.code) (auto simp: Suc_le_eq)
qed

lemma lset_lupt: \<open>lset (lupt i j) = {k. i \<le> k \<and> enat k < j}\<close>
  by (auto intro: lset_luptI dest: lset_luptD)

lemma llength_lupt[simp]: \<open>llength (lupt i j) = j - i\<close>
proof (coinduction arbitrary: i)
  case eq_enat
  then show ?case
  proof (cases j)
    case (enat nat)
    then show ?thesis
      by (subst (3) lupt.code) (auto simp: enat_0 enat_0_iff)
  next
    case infinity
    then show ?thesis
      by (subst (3) lupt.code) auto
  qed
qed

lemma lnth_lupt: \<open>k < j - enat i \<Longrightarrow> lnth (lupt i j) k = i + k\<close>
proof (induct k arbitrary: i)
  case 0
  then show ?case by (cases j) (auto simp add: lnth_0_conv_lhd)
next
  case (Suc k)
  from Suc(2) have \<open>enat k < j - Suc i\<close>
    by (cases j) auto
  with Suc(1)[OF this] Suc(2) show ?case
    by (subst lupt.code; cases j) auto
qed

lemma lmap_lupt_Suc: \<open>lmap f (lupt (Suc i) (eSuc j)) = lmap (f o Suc) (lupt i j)\<close>
  by (coinduction arbitrary: i j) (auto simp: eSuc_def split: enat.splits)

lemma llist_conv_lmap_lupt:
  \<open>lxs = lmap (lnth lxs) (lupt 0 (llength lxs))\<close>
  by (coinduction arbitrary: lxs)
    (auto simp: enat_0 lnth_0_conv_lhd llength_not_lnull lmap_lupt_Suc lnth_ltl)

lemma ldistinct_lupt[simp]: \<open>ldistinct (lupt i j)\<close>
  by (coinduction arbitrary: i) (auto simp: lset_lupt)

lemma lzip_lupt: \<open>lzip (lupt i j) (lupt i k) = lmap (\<lambda>x. (x, x)) (lupt i (min j k))\<close>
  by (coinduction arbitrary: i) (auto simp: min_def)

section \<open>Permutations of Lazy Lists\<close>

definition \<open>lpermute \<pi> lxs = lmap (\<lambda>i. lnth lxs (\<pi> i)) (lupt 0 (llength lxs))\<close>

abbreviation \<open>lbij_on \<pi> lxs \<equiv> bij_betw \<pi> {k. enat k < llength lxs} {k. enat k < llength lxs}\<close>

lemma lset_lpermute:
  assumes \<open>lbij_on \<pi> lxs\<close>
  shows \<open>lset (lpermute \<pi> lxs) = lset lxs\<close>
proof -
  have \<open>\<exists>m. lnth lxs n = lnth (lmap (\<lambda>i. lnth lxs (\<pi> i)) (lupt 0 (llength lxs))) m \<and> enat m < llength lxs\<close>
    if \<open>enat n < llength lxs\<close>
    for n :: nat
    using that assms bij_betw_inv_into_right[OF assms, of n]
    by (intro exI[of _ \<open>inv_into {k. enat k < llength lxs} \<pi> n\<close>])
      (auto 0 3 simp: lnth_lupt elim: bij_betwE[OF bij_betw_inv_into, THEN bspec, elim_format])
  with assms show ?thesis
    by (auto 0 3 simp: lpermute_def image_iff lset_lupt lset_conv_lnth lnth_lupt dest: bij_betwE)
qed

lemma llength_lpermute[simp]: \<open>llength (lpermute \<pi> lxs) = llength lxs\<close>
  by (auto simp: lpermute_def)

lemma lnth_lpermute[simp]: \<open>lbij_on \<pi> lxs \<Longrightarrow> i < llength lxs \<Longrightarrow> lnth (lpermute \<pi> lxs) i = lnth lxs (\<pi> i)\<close>
  by (simp add: lnth_lupt lpermute_def)

lemma lfilter_permute: \<open>ldistinct lxs \<Longrightarrow> ldistinct lys \<Longrightarrow> bij_betw \<pi> (lset lxs) (lset lys) \<Longrightarrow> \<forall>x \<in> lset lxs. P x \<longleftrightarrow> Q (\<pi> x) \<Longrightarrow>
  llength (lfilter P lxs) = llength (lfilter Q lys)\<close>
proof (coinduction arbitrary: lxs lys \<pi>)
  case eq_enat
  then have \<open>llength (lfilter P lxs) = 0 \<longleftrightarrow> llength (lfilter Q lys) = 0\<close>
    by (force simp: bij_betw_iff_bijections)
  moreover
  { assume *: \<open>llength (lfilter P lxs) \<noteq> 0\<close> \<open>llength (lfilter Q lys) \<noteq> 0\<close>
    then have lfin[unfolded comp_def, simp]: \<open>lfinite (ltakeWhile (Not o P) lxs)\<close> \<open>lfinite (ltakeWhile (Not o Q) lys)\<close>
      by (simp_all add: lfinite_ltakeWhile)
    let ?lxs = \<open>lappend (ltakeWhile (Not o P) lxs) (ltl (ldropWhile (Not o P) lxs))\<close>
    let ?lys = \<open>lappend (ltakeWhile (Not o Q) lys) (ltl (ldropWhile (Not o Q) lys))\<close>
    define x where \<open>x = lhd (ldropWhile (Not o P) lxs)\<close>
    with *(1) have \<open>P x\<close> using lhd_ldropWhile by force
    from *(1) have \<open>x \<in> lset lxs\<close> unfolding x_def
      by (metis in_lset_ldropWhileD lfilter_eq_LCons lhd_lfilter llength_eq_0 llist.exhaust_sel llist.set_intros(1) llist.set_sel(1))
    define y where \<open>y = lhd (ldropWhile (Not o Q) lys)\<close>
    with *(2) have \<open>Q y\<close> using lhd_ldropWhile by force
    from *(2) have \<open>y \<in> lset lys\<close> unfolding y_def
      by (metis in_lset_ldropWhileD lfilter_eq_LCons lhd_lfilter llength_eq_0 llist.exhaust_sel llist.set_intros(1) llist.set_sel(1))
    let ?\<pi> = \<open>\<pi>(inv_into (lset lxs) \<pi> y := \<pi> x)\<close>
    have
      \<open>epred (llength (lfilter P lxs)) = llength (lfilter P ?lxs)\<close>
      \<open>epred (llength (lfilter Q lys)) = llength (lfilter Q ?lys)\<close>
      by (auto simp add: epred_llength ltl_lfilter dest: lset_ltakeWhileD)
    moreover from eq_enat(1,2)
      lappend_ltakeWhile_ldropWhile[symmetric, of lxs \<open>Not o P\<close>, THEN arg_cong, of ldistinct, THEN iffD1, OF eq_enat(1)]
      lappend_ltakeWhile_ldropWhile[symmetric, of lys \<open>Not o Q\<close>, THEN arg_cong, of ldistinct, THEN iffD1, OF eq_enat(2)]
    have \<open>ldistinct ?lxs\<close> \<open>ldistinct ?lys\<close>
      by (auto simp add: ldistinct_lappend ldistinct_ldrop ldistinct_ltlI
          ldistinct_lprefix lprefix_ltakeWhile ldropWhile_eq_ldrop dest!: in_lset_ltlD)
    moreover
    have \<open>lxs = lappend (ltakeWhile (Not \<circ> P) lxs) (LCons x (ltl (ldropWhile (Not \<circ> P) lxs)))\<close>
      \<open>lys = lappend (ltakeWhile (Not \<circ> Q) lys) (LCons y (ltl (ldropWhile (Not \<circ> Q) lys)))\<close>
      using *(1,2) x_def y_def by force+
    with \<open>P x\<close> \<open>x \<in> lset lxs\<close> \<open>Q y\<close> \<open>y \<in> lset lys\<close>  eq_enat(1,2)
    have \<open>lset ?lxs = lset lxs - {x}\<close> \<open>lset ?lys = lset lys - {y}\<close>
      by (smt (verit, ccfv_SIG) Diff_insert_absorb Un_insert_right comp_eq_dest_lhs lset_ltakeWhileD
          in_lset_lappend_iff ldistinct_LCons ldistinct_lappend lset_LCons lset_lappend_conv)+
    with eq_enat(3,4) \<open>x \<in> lset lxs\<close> \<open>y \<in> lset lys\<close> have \<open>bij_betw ?\<pi> (lset ?lxs) (lset ?lys)\<close>
      by (auto elim!: bij_betw_singl_remap)
    moreover from eq_enat(4) \<open>P x\<close> \<open>Q y\<close> \<open>x \<in> lset lxs\<close> \<open>y \<in> lset lys\<close> have \<open>\<forall>x \<in> lset ?lxs. P x \<longleftrightarrow> Q (?\<pi> x)\<close>
      using bij_betw_inv_into_right[OF eq_enat(3), of y]
      by (auto simp: in_lset_lappend_iff lhd_ldropWhile_in_lset
          dest!: lset_ltakeWhileD in_lset_ldropWhileD in_lset_ltlD)
    note * = calculation this
  }
  ultimately show ?case
    by blast
qed

lemma count_llist_lpermute:
  \<open>lbij_on \<pi> lxs \<Longrightarrow> count_llist (lpermute \<pi> lxs) x = count_llist lxs x\<close>
  unfolding count_llist_alt
  by (subst (2) llist_conv_lmap_lupt[of lxs]) (auto simp: lpermute_def lfilter_lmap lset_lupt
      lfilter_permute[of \<open>lupt 0 (llength lxs)\<close> \<open>lupt 0 (llength lxs)\<close> \<pi> \<open>\<lambda>i. x = lnth lxs (\<pi> i)\<close> \<open>\<lambda>i. x = lnth lxs i\<close>])

lemma lpermute_lzip: \<open>lbij_on \<pi> lxs \<Longrightarrow> llength lys = llength lxs \<Longrightarrow> lpermute \<pi> (lzip lxs lys) = lzip (lpermute \<pi> lxs) (lpermute \<pi> lys)\<close>
  by (auto simp: lpermute_def lzip_lmap_same lzip_lupt llist.map_comp lset_lupt lnth_lzip bij_betw_iff_bijections intro!: llist.map_cong)

lemma exist_nth_occurrence_in_llist:
  \<open>count_llist lxs x > n \<Longrightarrow> \<exists>i < llength lxs. lnth lxs i = x \<and> count_list (ltaken i lxs) x = n\<close>
proof (induct n arbitrary: lxs)
  case 0
  then have ex: \<open>\<exists>i < llength lxs. lnth lxs i = x\<close>
    by (metis in_lset_conv_lnth in_lset_iff_count_llist not_gr_zero zero_enat_def)
  define i where \<open>i = (LEAST i. enat i < llength lxs \<and> lnth lxs i = x)\<close>
  have i: \<open>enat i < llength lxs\<close> \<open>lnth lxs i = x\<close>
    \<open>\<And>j. enat j < llength lxs \<Longrightarrow> lnth lxs j = x \<Longrightarrow> i \<le> j\<close>
    unfolding i_def using LeastI2_wellorder_ex[OF ex]
    by (force simp: Least_le)+
  moreover have \<open>lnth lxs i = lnth lxs j \<Longrightarrow> j < i \<Longrightarrow> False\<close> for j
    using i by (metis order.strict_trans enat_ord_simps(2) less_le_not_le)
  ultimately show ?case
    by (force simp: count_list_0_iff set_ltaken_conv intro!: exI[of _ i])
next
  case (Suc n)
  let ?lxs = \<open>ltl (ldropWhile ((\<noteq>) x) lxs)\<close>
  from Suc(2) have \<open>enat n < count_llist ?lxs x\<close>
    by (metis Suc_ile_eq count_llist_code iless_Suc_eq not_less_zero)
  with Suc(1) obtain i where i: \<open>enat i < llength ?lxs\<close>
    \<open>lnth ?lxs i = x\<close> \<open>count_list (ltaken i ?lxs) x = n\<close>
    by blast
  from Suc(2) obtain k where k: \<open>llength (ltakeWhile ((\<noteq>) x) lxs) = enat k\<close>
    by (metis (full_types) enat_the_enat in_lset_iff_count_llist llength_ltakeWhile_eq_infinity
        lset_ltakeWhileD not_less_zero)
  then have klen: \<open>enat k < llength lxs\<close>
    by (metis gr_implies_not_zero i(1) ldropWhile_eq_ldrop ldrop_eq_LNil llength_LNil
        lprefix_llength_le lprefix_ltakeWhile ltl_simps(1) order_neq_le_trans)
  let ?i = \<open>k + Suc i\<close>
  have lxs: \<open>lxs = lappend (ltakeWhile ((\<noteq>) x) lxs) (LCons x ?lxs)\<close>
    by (metis Suc(2) in_lset_iff_count_llist ltakeWhile_ldropWhile_decomp not_less_zero)
  have \<open>enat ?i < llength lxs\<close>
    by (subst lxs) (metis eSuc_enat enat_less_enat_plusI2 i(1) ileI1 iless_Suc_eq k llength_LCons
        llength_lappend)
  moreover from k i(2) have \<open>lnth lxs ?i = x\<close>
    by (subst lxs) (auto simp: lnth_lappend)
  moreover have x: \<open>x \<notin> lset (ltakeWhile ((\<noteq>) x) lxs)\<close>
    by (metis (full_types) lset_ltakeWhileD)
  with k llength_ltakeWhile_le[of \<open>(\<noteq>) x\<close> lxs] have \<open>x \<notin> set (ltaken k lxs)\<close>
    by (subst set_ltaken_conv) (auto simp: in_lset_conv_lnth ltakeWhile_nth)
  with k klen i(3) x have \<open>count_list (ltaken ?i lxs) x = Suc n\<close>
    using [[simproc del: list_to_set_comprehension]]
    by (subst lxs) (auto simp: ltaken_lappend dest!: set_mp[OF set_ltaken] intro!: count_notin split: llist.splits)
  ultimately show ?case by blast
qed

function lfind_index where
  \<open>lfind_index n x i lxs = (if count_llist lxs x \<le> enat n then i else
    if lhd lxs = x then case n of 0 \<Rightarrow> i | Suc m \<Rightarrow> lfind_index m x (Suc i) (ltl lxs)
    else lfind_index n x (Suc i) (ltl lxs))\<close>
  by auto
termination
proof (relation \<open>measure (\<lambda>(n, x, _, lxs). LEAST i. enat i < llength lxs \<and> lnth lxs i = x \<and> count_list (ltaken i lxs) x = n)\<close>)
  fix n x i and lxs :: \<open>'a llist\<close> and m
  assume hlt: \<open>\<not> count_llist lxs x \<le> enat n\<close>
  assume hlhd: \<open>lhd lxs = x\<close>
  assume hn: \<open>n = Suc m\<close>
  let ?PP = \<open>\<lambda>x lxs k n. enat k < llength lxs \<and> lnth lxs k = x \<and> count_list (ltaken k lxs) x = n\<close>
  let ?P = \<open>?PP x\<close>
  from hlt hn have hcount: \<open>enat (Suc m) < count_llist lxs x\<close>
    by (simp add: not_le)
  obtain j where hj1: \<open>enat j < llength lxs\<close> and hj2: \<open>lnth lxs j = x\<close>
      and hj3: \<open>enat (count_list (ltaken j lxs) x) = enat (Suc m)\<close>
    using exist_nth_occurrence_in_llist[OF hcount] by blast
  have hj3': \<open>count_list (ltaken j lxs) x = Suc m\<close>
    using hj3 by simp
  have rhs_eq: \<open>(LEAST k. ?P lxs k (Suc m)) = Suc (LEAST k. ?P lxs (Suc k) (Suc m))\<close>
  proof (rule Least_Suc)
    show \<open>?P lxs j (Suc m)\<close>
      using hj1 hj2 hj3' by simp
    show \<open>\<not> ?P lxs 0 (Suc m)\<close>
      by simp
  qed
  have lhs_eq: \<open>(LEAST k. ?P (ltl lxs) k m) = (LEAST k. ?P lxs (Suc k) (Suc m))\<close>
    using hlhd by (cases lxs) (auto simp: Suc_ile_eq lnth_LCons' fun_eq_iff gr0_conv_Suc)
  have key2: \<open>(LEAST k. ?P lxs k (Suc m)) = Suc (LEAST k. ?P (ltl lxs) k m)\<close>
    using rhs_eq lhs_eq by simp
  show \<open>((m, x, Suc i, ltl lxs), n, x, i, lxs) \<in> measure (\<lambda>(n, x, _, lxs). LEAST i. ?PP x lxs i n)\<close>
    by (simp add: hn key2)
next
  fix n x i and lxs :: \<open>'a llist\<close>
  assume hlt: \<open>\<not> count_llist lxs x \<le> enat n\<close>
  assume hlhd: \<open>lhd lxs \<noteq> x\<close>
  let ?PP = \<open>\<lambda>x lxs k n. enat k < llength lxs \<and> lnth lxs k = x \<and> count_list (ltaken k lxs) x = n\<close>
  let ?P = \<open>?PP x\<close>
  from hlt have hcount: \<open>enat n < count_llist lxs x\<close>
    by (simp add: not_le)
  obtain j where hj1: \<open>enat j < llength lxs\<close> and hj2: \<open>lnth lxs j = x\<close>
      and hj3: \<open>enat (count_list (ltaken j lxs) x) = enat n\<close>
    using exist_nth_occurrence_in_llist[OF hcount] by blast
  have hj3': \<open>count_list (ltaken j lxs) x = n\<close>
    using hj3 by simp
  have rhs_eq: \<open>(LEAST k. ?P lxs k n) = Suc (LEAST k. ?P lxs (Suc k) n)\<close>
  proof (rule Least_Suc)
    show \<open>?P lxs j n\<close>
      using hj1 hj2 hj3' by simp
    show \<open>\<not> ?P lxs 0 n\<close>
      using hlhd by (cases lxs) (auto simp: lhd_conv_lnth enat_0)
  qed
  have lhs_eq: \<open>(LEAST k. ?P (ltl lxs) k n) = (LEAST k. ?P lxs (Suc k) n)\<close>
    using hlhd by (cases lxs) (auto simp: Suc_ile_eq lnth_LCons' fun_eq_iff gr0_conv_Suc)
  show \<open>((n, x, Suc i, ltl lxs), n, x, i, lxs) \<in> measure (\<lambda>(n, x, _, lxs). LEAST i. ?PP x lxs i n)\<close>
    by (simp add: lhs_eq rhs_eq less_Suc_eq_le)
qed simp
declare lfind_index.simps[simp del]

lemma lfind_index_ge[simp]: \<open>lfind_index n x j lxs \<ge> j\<close>
proof (induct n x j lxs rule: lfind_index.induct)
  case (1 n x i lxs)
  then show ?case 
    by (subst lfind_index.simps) (auto dest: Suc_leD split: nat.splits)
qed

lemma lfind_index_less[simp]: \<open>count_llist lxs x > enat n \<Longrightarrow> lfind_index n x j lxs < llength lxs + j\<close>
proof (induct n x j lxs rule: lfind_index.induct)
  case (1 n x i lxs)
  then show ?case 
    by (subst lfind_index.simps; cases lxs)
      (auto split: nat.splits simp: enat_0 count_llist_zero_iff Suc_ile_eq eSuc_plus iadd_Suc_right
        simp flip: eSuc_enat)
qed

lemma lfind_index_lnth:
  \<open>count_llist lxs x > enat n \<Longrightarrow> lnth lxs (lfind_index n x j lxs - j) = x\<close>
proof (induct n x j lxs rule: lfind_index.induct)
  case (1 n x i lxs)
  show ?case
  proof -
    note IH1 = 1(1)
    note IH2 = 1(2)
    from 1(3) have hcount: \<open>enat n < count_llist lxs x\<close> by simp
    have hlt: \<open>\<not> count_llist lxs x \<le> enat n\<close> using hcount by simp
    obtain h t where hlxs: \<open>lxs = LCons h t\<close>
      using hcount by (cases lxs) (auto simp: count_llist_zero_iff)
    have step1: \<open>lfind_index n x i lxs =
      (if lhd lxs = x then case n of 0 \<Rightarrow> i | Suc m \<Rightarrow> lfind_index m x (Suc i) (ltl lxs)
       else lfind_index n x (Suc i) (ltl lxs))\<close>
      by (subst lfind_index.simps) (simp add: hlt)
    show ?thesis
    proof (cases \<open>h = x\<close>)
      case hx: True
      show ?thesis
      proof (cases n)
        case 0
        with hx hlxs hlt step1 show ?thesis by simp
      next
        case (Suc m)
        have cnt_t: \<open>enat m < count_llist t x\<close>
          using hcount hlxs hx Suc by (simp add: Suc_ile_eq)
        have ih: \<open>lnth t (lfind_index m x (Suc i) t - Suc i) = x\<close>
          using IH1[of m] hlt hlxs hx Suc cnt_t by simp
        have \<open>Suc i \<le> lfind_index m x (Suc i) t\<close> by simp
        then have \<open>\<not> lfind_index m x (Suc i) t \<le> i\<close> by linarith
        then show ?thesis
          using ih hx hlxs Suc step1 by (simp add: lnth_LCons')
      qed
    next
      case hx: False
      have cnt_t: \<open>enat n < count_llist t x\<close>
        using hcount hlxs hx by simp
      have ih: \<open>lnth t (lfind_index n x (Suc i) t - Suc i) = x\<close>
        using IH2 hlt hlxs hx cnt_t by simp
      have \<open>Suc i \<le> lfind_index n x (Suc i) t\<close> by simp
      then have \<open>\<not> lfind_index n x (Suc i) t \<le> i\<close> by linarith
      then show ?thesis
        using ih hx hlxs step1 by (simp add: lnth_LCons')
    qed
  qed
qed

lemma ltaken_LCons:
  \<open>ltaken i (LCons x lxs) = (case i of 0 \<Rightarrow> [] | Suc j \<Rightarrow> x # ltaken j lxs)\<close>
  by (cases i; simp)

lemma lfind_index_count_list:
  \<open>count_llist lxs x > n \<Longrightarrow> count_list (ltaken (lfind_index n x j lxs - j) lxs) x = n\<close>
proof (induct n x j lxs rule: lfind_index.induct)
  case (1 n x i lxs)
  show ?case
  proof -
    note IH1 = 1(1)
    note IH2 = 1(2)
    from 1(3) have hcount: \<open>enat n < count_llist lxs x\<close> by simp
    have hlt: \<open>\<not> count_llist lxs x \<le> enat n\<close> using hcount by simp
    obtain h t where hlxs: \<open>lxs = LCons h t\<close>
      using hcount by (cases lxs) (auto simp: count_llist_zero_iff)
    have step1: \<open>lfind_index n x i lxs =
      (if lhd lxs = x then case n of 0 \<Rightarrow> i | Suc m \<Rightarrow> lfind_index m x (Suc i) (ltl lxs)
       else lfind_index n x (Suc i) (ltl lxs))\<close>
      by (subst lfind_index.simps) (simp add: hlt)
    show ?thesis
    proof (cases \<open>h = x\<close>)
      case hx: True
      show ?thesis
      proof (cases n)
        case 0
        with hx hlxs step1 show ?thesis by (simp add: ltaken_LCons)
      next
        case (Suc m)
        have cnt_t: \<open>enat m < count_llist t x\<close>
          using hcount hlxs hx Suc by (simp add: Suc_ile_eq)
        have ih: \<open>count_list (ltaken (lfind_index m x (Suc i) t - Suc i) t) x = m\<close>
          using IH1[of m] hlt hlxs hx Suc cnt_t by simp
        have ge: \<open>Suc i \<le> lfind_index m x (Suc i) t\<close> by simp
        have nle: \<open>\<not> lfind_index m x (Suc i) t \<le> i\<close> using ge by linarith
        have diff_eq: \<open>lfind_index m x (Suc i) t - i = Suc (lfind_index m x (Suc i) t - Suc i)\<close>
          using ge by arith
        show ?thesis
          using ih nle hx hlxs Suc step1 diff_eq by (simp add: ltaken_LCons)
      qed
    next
      case hx: False
      have cnt_t: \<open>enat n < count_llist t x\<close>
        using hcount hlxs hx by simp
      have ih: \<open>count_list (ltaken (lfind_index n x (Suc i) t - Suc i) t) x = n\<close>
        using IH2 hlt hlxs hx cnt_t by simp
      have ge: \<open>Suc i \<le> lfind_index n x (Suc i) t\<close> by simp
      have nle: \<open>\<not> lfind_index n x (Suc i) t \<le> i\<close> using ge by linarith
      have diff_eq: \<open>lfind_index n x (Suc i) t - i = Suc (lfind_index n x (Suc i) t - Suc i)\<close>
        using ge by arith
      show ?thesis
        using ih nle hx hlxs step1 diff_eq by (simp add: ltaken_LCons)
    qed
  qed
qed

lemma lnth_equalityI: \<open>llength lxs = llength lys \<Longrightarrow> (\<And>i. enat i < llength lxs \<Longrightarrow> lnth lxs i = lnth lys i) \<Longrightarrow> lxs = lys\<close>
  by (metis (full_types) llist.rel_eq llist_all2_all_lnthI)

lemma lfind_index_inject:
  \<open>count_llist lxs x > enat n \<Longrightarrow> count_llist lxs y > enat m \<Longrightarrow>
   lfind_index n x j lxs = lfind_index m y j lxs \<Longrightarrow> n = m \<and> x = y\<close>
  by (metis lfind_index_count_list lfind_index_lnth)

lemma count_list_ltaken_less:
  \<open>i < llength lxs \<Longrightarrow> count_list (ltaken i lxs) (lnth lxs i) < count_llist lxs (lnth lxs i)\<close>
proof (induct i arbitrary: lxs)
  case 0
  then show ?case
    by (auto simp: enat_0 count_llist_zero_iff lnth_0_conv_lhd)
next
  case (Suc i)
  then show ?case
    by (cases lxs) (auto simp flip: eSuc_enat)
qed

lemma count_list_inject:
  \<open>enat i < llength lxs \<Longrightarrow> enat j < llength lxs \<Longrightarrow>
  count_list (ltaken i lxs) (lnth lxs j) = count_list (ltaken j lxs) (lnth lxs j) \<Longrightarrow>
  lnth lxs i = lnth lxs j \<Longrightarrow> i = j\<close>
  by (induct i arbitrary: j lxs)
    (auto simp: count_list_0_iff set_ltaken_conv image_iff ltaken_LCons Suc_ile_eq Ball_def split: llist.splits if_splits nat.splits)

section \<open>Same-Count Equivalence Relation\<close>

definition \<open>eq_cmset lxs lys = (\<forall>x. count_llist lxs x = count_llist lys x)\<close>

lemma lset_eq_cmset: \<open>eq_cmset lxs lys \<Longrightarrow> lset lxs = lset lys\<close>
  by (auto simp: eq_cmset_def in_lset_iff_count_llist)

lemma eq_cmset_llength: \<open>eq_cmset lxs lys \<Longrightarrow> llength lxs = llength lys\<close>
  unfolding eq_cmset_def
proof (coinduction arbitrary: lxs lys)
  case eq_enat
  then have heq: \<open>\<forall>x. count_llist lxs x = count_llist lys x\<close> by blast
  have lnull_iff: \<open>lnull lxs \<longleftrightarrow> lnull lys\<close>
    using heq by (auto simp: lnull_def count_llist_zero_iff)
  show ?case
  proof (cases \<open>lnull lxs\<close>)
    case True
    then show ?thesis using lnull_iff by (auto simp: epred_llength)
  next
    case lxs_ne: False
    then obtain h t where hlxs: \<open>lxs = LCons h t\<close> by (cases lxs) auto
    from lnull_iff lxs_ne have \<open>\<not> lnull lys\<close> by simp
    then have h_in_lys: \<open>h \<in> lset lys\<close>
    proof -
      have hpos: \<open>0 < count_llist lxs h\<close> by (simp add: hlxs)
      have \<open>0 < count_llist lys h\<close> using heq hpos by simp
      then show ?thesis by (simp add: in_lset_iff_count_llist)
    qed
    let ?lys' = \<open>lappend (ltakeWhile ((\<noteq>) h) lys) (ltl (ldropWhile ((\<noteq>) h) lys))\<close>
    have lys_decomp: \<open>lys = lappend (ltakeWhile ((\<noteq>) h) lys) (LCons h (ltl (ldropWhile ((\<noteq>) h) lys)))\<close>
      using h_in_lys by (metis ltakeWhile_ldropWhile_decomp)
    have epred_lxs: \<open>epred (llength lxs) = llength t\<close>
      by (simp add: hlxs epred_llength)
    have epred_lys: \<open>epred (llength lys) = llength ?lys'\<close>
      by (subst lys_decomp) (simp add: iadd_Suc_right)
    have lfinite_take: \<open>lfinite (ltakeWhile ((\<noteq>) h) lys)\<close>
      by (simp add: lfinite_ltakeWhile) (use h_in_lys in blast)
    have h_not_in_take: \<open>count_llist (ltakeWhile ((\<noteq>) h) lys) h = 0\<close>
      by (force simp: count_llist_zero_iff dest: lset_ltakeWhileD)
    have heq': \<open>\<forall>x. count_llist t x = count_llist ?lys' x\<close>
    proof
      fix x
      have hx: \<open>count_llist (LCons h t) x = count_llist lys x\<close>
        using heq hlxs by blast
      have lys_x: \<open>count_llist lys x =
          count_llist (ltakeWhile ((\<noteq>) h) lys) x +
          count_llist (LCons h (ltl (ldropWhile ((\<noteq>) h) lys))) x\<close>
        by (subst lys_decomp) (simp add: count_llist_lappend lfinite_take)
      show \<open>count_llist t x = count_llist ?lys' x\<close>
        using hx lys_x h_not_in_take lfinite_take
        by (simp add: count_llist_lappend split: if_splits)
    qed
    show ?thesis
      using lnull_iff epred_lxs epred_lys heq'
      using llength_eq_0 by blast
  qed
qed

lemma eq_cmset_alt: \<open>eq_cmset lxs' lxs \<longleftrightarrow> (\<exists>\<pi>. lbij_on \<pi> lxs \<and> lpermute \<pi> lxs = lxs')\<close>
proof
  assume h: \<open>\<exists>\<pi>. lbij_on \<pi> lxs \<and> lpermute \<pi> lxs = lxs'\<close>
  then obtain \<pi> where h\<pi>: \<open>lbij_on \<pi> lxs\<close> \<open>lpermute \<pi> lxs = lxs'\<close> by blast
  then show \<open>eq_cmset lxs' lxs\<close>
    unfolding eq_cmset_def by (auto simp: count_llist_lpermute fun_eq_iff)
next
  assume h: \<open>eq_cmset lxs' lxs\<close>
  then have hlen: \<open>llength lxs = llength lxs'\<close>
    using eq_cmset_llength[of lxs' lxs, symmetric] by blast
  then have hcount: \<open>\<forall>x. count_llist lxs' x = count_llist lxs x\<close>
    using h unfolding eq_cmset_def by (auto simp: fun_eq_iff)
  define f where \<open>f = (\<lambda>i. let x = lnth lxs' i in lfind_index (count_list (ltaken i lxs') x) x 0 lxs)\<close>
  have hgt: \<open>\<And>i. enat i < llength lxs \<Longrightarrow>
      enat (count_list (ltaken i lxs') (lnth lxs' i)) < count_llist lxs (lnth lxs' i)\<close>
    using hlen hcount by (metis count_list_ltaken_less)
  show \<open>\<exists>\<pi>. lbij_on \<pi> lxs \<and> lpermute \<pi> lxs = lxs'\<close>
  proof (intro exI[of _ f] conjI)
    show \<open>lbij_on f lxs\<close>
    proof (rule bij_betwI'[where f = f and X = \<open>{k. enat k < llength lxs}\<close> and Y = \<open>{k. enat k < llength lxs}\<close>])
      fix i j
      assume hi: \<open>i \<in> {k. enat k < llength lxs}\<close> and hj: \<open>j \<in> {k. enat k < llength lxs}\<close>
      show \<open>(f i = f j) = (i = j)\<close>
      proof
        assume hfij: \<open>f i = f j\<close>
        have hi': \<open>enat (count_list (ltaken i lxs') (lnth lxs' i)) < count_llist lxs (lnth lxs' i)\<close>
          using hgt hi by simp
        have hj': \<open>enat (count_list (ltaken j lxs') (lnth lxs' j)) < count_llist lxs (lnth lxs' j)\<close>
          using hgt hj by simp
        have heq: \<open>lfind_index (count_list (ltaken i lxs') (lnth lxs' i)) (lnth lxs' i) 0 lxs =
                   lfind_index (count_list (ltaken j lxs') (lnth lxs' j)) (lnth lxs' j) 0 lxs\<close>
          using hfij unfolding f_def Let_def by simp
        from lfind_index_inject[OF hi' hj' heq]
        have heqx: \<open>lnth lxs' i = lnth lxs' j\<close>
          and heqn: \<open>count_list (ltaken i lxs') (lnth lxs' i) = count_list (ltaken j lxs') (lnth lxs' j)\<close>
          by auto
        show \<open>i = j\<close>
          using hi hj hlen heqx heqn by (metis count_list_inject mem_Collect_eq)
      next
        assume \<open>i = j\<close> then show \<open>f i = f j\<close> by simp
      qed
    next
      fix i assume hi: \<open>i \<in> {k. enat k < llength lxs}\<close>
      show \<open>f i \<in> {k. enat k < llength lxs}\<close>
        unfolding f_def Let_def
        using hgt[OF] hi
        by (metis add.right_neutral lfind_index_less mem_Collect_eq zero_enat_def)
    next
      fix k assume hk: \<open>k \<in> {k. enat k < llength lxs}\<close>
      show \<open>\<exists>i \<in> {k. enat k < llength lxs}. k = f i\<close>
        unfolding f_def Let_def
        by (metis add.right_neutral count_list_inject count_list_ltaken_less diff_zero hcount hk
            hlen lfind_index_count_list lfind_index_less lfind_index_lnth mem_Collect_eq zero_enat_def)
    qed
  next
    show \<open>lpermute f lxs = lxs'\<close>
    proof (intro lnth_equalityI)
      show \<open>llength (lpermute f lxs) = llength lxs'\<close>
        by (simp add: lpermute_def hlen)
    next
      fix i
      assume hi: \<open>enat i < llength (lpermute f lxs)\<close>
      then have hi': \<open>enat i < llength lxs\<close> by (simp add: lpermute_def lnth_lupt)
      have \<open>lnth (lpermute f lxs) i = lnth lxs (f i)\<close>
        by (simp add: lpermute_def lnth_lupt hi' f_def Let_def)
      also have \<open>\<dots> = lnth lxs' i\<close>
      proof -
        have hlt: \<open>enat (count_list (ltaken i lxs') (lnth lxs' i)) < count_llist lxs (lnth lxs' i)\<close>
          using hgt hi' by blast
        from lfind_index_lnth[OF hlt, of 0] show ?thesis
          unfolding f_def Let_def by simp
      qed
      finally show \<open>lnth (lpermute f lxs) i = lnth lxs' i\<close> .
    qed
  qed
qed

lemma eq_cmset_lzip_left:
  assumes \<open>eq_cmset lxs' lxs\<close> \<open>llength lys = llength lxs\<close>
  shows \<open>\<exists>lys'. eq_cmset (lzip lxs' lys') (lzip lxs lys) \<and> llength lys' = llength lxs'\<close>
proof -
  from assms(1) obtain \<pi> where \<open>lbij_on \<pi> lxs\<close> \<open>lpermute \<pi> lxs = lxs'\<close> unfolding eq_cmset_alt
    by blast
  with assms(2) show ?thesis
    by (intro exI[of _ \<open>lpermute \<pi> lys\<close>]) (auto simp: lpermute_lzip eq_cmset_alt intro!: exI[of _ \<pi>])
qed

lemma eq_cmset_lmap:
  assumes \<open>eq_cmset lxs lys\<close>
  shows \<open>eq_cmset (lmap f lxs) (lmap f lys)\<close>
proof -
  from assms obtain \<pi> where \<open>lbij_on \<pi> lys\<close> \<open>lpermute \<pi> lys = lxs\<close> unfolding eq_cmset_alt
    by blast
  then show ?thesis
    by (force simp: lpermute_def llist.map_comp lset_lupt eq_cmset_alt
        dest: bij_betwE intro!: llist.map_cong exI[where x = \<pi>] lnth_lmap)
qed

lemma llist_all2_reorder_left_invariance:
  assumes rel: \<open>llist_all2 R lxs lys\<close> and ms_x: \<open>eq_cmset lxs' lxs\<close>
  shows \<open>\<exists>lys'. llist_all2 R lxs' lys' \<and> eq_cmset lys' lys\<close>
proof -
  from ms_x rel[THEN llist_all2_llengthD] obtain lys' where
    ms_xy: \<open>eq_cmset (lzip lxs' lys') (lzip lxs lys)\<close> and len: \<open>llength lys' = llength lxs'\<close>
    by (metis eq_cmset_lzip_left)
  with rel have rel': \<open>llist_all2 R lxs' lys'\<close> unfolding llist_all2_conv_lzip
    by (auto simp: lset_eq_cmset)
  moreover from eq_cmset_lmap[OF ms_xy, of snd]
  have \<open>eq_cmset (lmap snd (lzip lxs' lys')) (lmap snd (lzip lxs lys))\<close> .
  with rel[THEN llist_all2_llengthD] rel'[THEN llist_all2_llengthD] have \<open>eq_cmset lys' lys\<close>
    by (auto simp: lmap_snd_lzip_conv_ltake ltake_all)
  ultimately show ?thesis
    by blast
qed

section \<open>Countable Multisets as a Quotient\<close>

quotient_type 'a cmset = \<open>'a llist\<close> / eq_cmset
  by (auto simp: eq_cmset_def intro!: equivpI reflpI sympI transpI)

lift_bnf (cmset: 'a) cmset
  for map: cmimage rel: cmrel
proof -
  fix P :: \<open>'a \<Rightarrow> 'b \<Rightarrow> bool\<close> and Q :: \<open>'b \<Rightarrow> 'c \<Rightarrow> bool\<close>
  show \<open>llist_all2 P OO eq_cmset OO llist_all2 Q
       \<le> eq_cmset OO llist_all2 (P OO Q) OO eq_cmset\<close>
  proof safe
    fix l r l' r'
    assume \<open>llist_all2 P l l'\<close> \<open>eq_cmset l' r'\<close> \<open>llist_all2 Q r' r\<close>
    with llist_all2_reorder_left_invariance[OF this(3,2)]
    show \<open>(eq_cmset OO llist_all2 (P OO Q) OO eq_cmset) l r\<close>
      by (auto intro!: relcomppI[of _ _ l] simp: eq_cmset_def llist.rel_compp)
  qed
next
  fix S :: \<open>'a set set\<close>
  assume \<open>S \<noteq> {}\<close>
  then show \<open>(\<Inter>As\<in>S. {(x, x'). eq_cmset x x'} `` {x. lset x \<subseteq> As})
          \<subseteq> {(x, x'). eq_cmset x x'} `` {x. lset x \<subseteq> \<Inter> S}\<close>
    using Inter_greatest[of S \<open>lset _\<close>] lset_eq_cmset
    unfolding subset_eq Ball_def Bex_def INT_iff Image_iff mem_Collect_eq prod.case
    by (metis cmset.abs_eq_iff)
qed

section \<open>Lazy List Interleaving\<close>

context notes [[function_internals]]
begin
partial_function (llist) lflat where
  \<open>lflat lxss = (case lxss of LNil \<Rightarrow> LNil | LCons xs lxss \<Rightarrow> lappend (llist_of xs) (lflat lxss))\<close>
end

lemma ltaken_ldropn_decomp: \<open>lxs = lappend (llist_of (ltaken n lxs)) (ldropn n lxs)\<close>
  by (induct n arbitrary: lxs) (auto split: llist.splits)

lemma count_llist_llist_of[simp]: \<open>count_llist (llist_of xs) x = count_list xs x\<close>
  by (induct xs) (auto simp: enat_0 simp flip: eSuc_enat)

lemma lmap_lfilter_swap: \<open>\<forall>x \<in> lset lxs. P x \<longleftrightarrow> Q (f x) \<Longrightarrow> lmap f (lfilter P lxs) = lfilter Q (lmap f lxs)\<close>
  by (induct lxs) auto


lemma lsum_lmap_zero: \<open>lsum (lmap (\<lambda>z. 0) lxs) = 0\<close>
proof -
  have \<open>lset (lmap (\<lambda>z. 0::enat) lxs) \<subseteq> {0}\<close> by fastforce
  then have \<open>ldropWhile ((=) 0) (lmap (\<lambda>z. 0) lxs) = LNil\<close>
    by (simp add: ldropWhile_eq_LNil_iff)
  then show ?thesis
    by (metis llist.case(1) lsum_code_alt)
qed

lemma lsum_LNil[simp]: \<open>lsum LNil = 0\<close>
  by (simp add: lsum_code_alt)

lemma lsum_LCons[simp]: \<open>lsum (LCons x lxs) = x + lsum lxs\<close>
  by (simp add: lsum_code_alt)

lemma count_llist_lmap_const:
  \<open>count_llist (lmap (\<lambda>z. a) lxs) x = (if x = a then llength lxs else 0)\<close>
  unfolding count_llist_alt
  by (auto simp: lfilter_lmap)

lemma lsum_lmap_all_but_one_0: \<open>x \<in> lset lxs \<Longrightarrow> ldistinct lxs \<Longrightarrow> lsum (lmap (\<lambda>z. if z = x then y else 0) lxs) = y\<close>
proof (induct x lxs rule: llist.set_induct)
  case (LCons1 x' lxs)
  then have \<open>lmap (\<lambda>z. if z = x' then y else 0) lxs = lmap (\<lambda>_. 0) lxs\<close>
    by (intro llist.map_cong) auto
  then show ?case
    by (auto simp: lsum_lmap_zero)
next
  case (LCons2 x' lxs x)
  then show ?case
    by auto
qed

lemma ltaken_Suc:
  \<open>ltaken (Suc i) lxs = (if i < llength lxs then ltaken i lxs @ [lnth lxs i] else ltaken i lxs)\<close>
proof (induct i arbitrary: lxs)
  case 0
  then show ?case
    by (auto simp: enat_0 Suc_ile_eq split: if_splits llist.splits)
next
  case (Suc i)
  then show ?case
    by (cases lxs) (auto simp: enat_0 Suc_ile_eq split: if_splits llist.splits)
qed

lemma ltaken_all_same: \<open>enat n \<ge> llength lxs \<Longrightarrow> enat m \<ge> llength lxs \<Longrightarrow> ltaken n lxs = ltaken m lxs\<close>
  by (metis lappend_LNil2 ldropn_eq_LNil llist_of_inject ltaken_ldropn_decomp)

lemma lsum_mono: \<open>lprefix lxs lys \<Longrightarrow> lsum lxs \<le> lsum lys\<close>
proof -
  assume \<open>lprefix lxs lys\<close>
  show \<open>lsum lxs \<le> lsum lys\<close>
  proof (cases \<open>lfinite lxs\<close>)
    case True
    then show ?thesis 
      using `lprefix lxs lys` `lfinite lxs`
      by (induct lxs arbitrary: lys rule: lfinite.induct) (auto simp: LCons_lprefix_conv)
  next
    case False
    then show ?thesis 
      using `lprefix lxs lys`
      by (simp add: not_lfinite_lprefix_conv_eq)
  qed
qed

lemma Sup_enat_remove0: \<open>\<exists>x \<in> X. x > 0 \<Longrightarrow> Sup (X :: enat set) = Sup (X - {0})\<close>
proof -
  assume ex: \<open>(\<exists>x \<in> X. x > 0)\<close>
  show \<open>Sup (X :: enat set) = Sup (X - {0})\<close>
    unfolding Sup_enat_def
    by (smt (verit, ccfv_threshold) Diff_empty Diff_insert0 Max.remove empty_iff finite.emptyI
        finite_Diff_insert max_enat_simps(3))
qed

lemma lSup_eq_lappend: \<open>Complete_Partial_Order.chain lprefix Y \<Longrightarrow> \<exists>lys \<in> Y. lprefix (llist_of xs) lys \<Longrightarrow>
  lSup Y = lappend (llist_of xs) (lSup (ldropn (length xs) ` Y))\<close>
proof (induct xs arbitrary: Y)
  case (Cons a xs)
  from Cons(3) obtain lys where lys: \<open>\<not> lnull lys\<close> \<open>lys \<in> Y\<close> \<open>lhd lys = a\<close> \<open>lprefix (llist_of xs) (ltl lys)\<close>
    by (metis eq_LConsD llist_of.simps(2) llist_of_eq_LNil_conv lnull_llist_of lprefix.cases
        lprefix_not_lnullD)
  from Cons(2-) have lhd_Y: \<open>lys \<in> Y \<Longrightarrow> \<not> lnull lys ==> lhd lys = a\<close> for lys
    by (metis eq_LConsD lhd_lSup_eq llist.disc(2) llist_of.simps(2) lprefix_lhdD
        lprefix_not_lnullD)
  from Cons(2-) have lhd_lSup[simp]: \<open>lhd (lSup Y) = a\<close>
    by (metis lhd_LCons lhd_lSup_eq llist.disc(2) llist_of.simps(2) lprefix_lhdD lprefix_lnull)
  moreover have \<open>lSup (ltl ` (Y \<inter> {l. \<not> lnull l})) =
          lappend (llist_of xs) (lSup (ldropn (Suc (length xs)) ` Y))\<close>
  proof -
    have \<open>ldropn (Suc (length xs)) ` (Y \<inter> {l. \<not> lnull l}) \<subseteq> ldropn (Suc (length xs)) ` Y\<close>
      (is \<open>?lhs \<subseteq> ?rhs\<close>) by auto
    moreover have \<open>?rhs  - {LNil} \<subseteq> ?lhs\<close>
      by auto
    ultimately have \<open>lSup ?lhs = lSup ?rhs\<close>
      by (metis Int_Diff inf.absorb_iff2 inf.order_iff lSup_minus_LNil)
    moreover have chain_ltl: \<open>Complete_Partial_Order.chain lprefix (ltl ` (Y \<inter> {l. \<not> lnull l}))\<close>
      by (metis chain_lprefix_ltl Cons.prems(1))
    moreover have \<open>Bex (ltl ` (Y \<inter> {l. \<not> lnull l})) (lprefix (llist_of xs))\<close>
      by (auto intro!: bexI[of _ lys] simp: lys)
    ultimately show ?thesis
      by (subst Cons(1)) (auto simp: image_image ldropn_ltl)
  qed
  ultimately show ?case
    by (subst lSup.code)
      (auto simp: LCons_lprefix_conv lhd_Y lys intro!: the1_equality bexI[of _ lys])
qed simp

lemma lsum_0D: \<open>x \<in> lset lxs \<Longrightarrow> lsum lxs = 0 \<Longrightarrow> x = 0\<close>
  by (induct x lxs rule: llist.set_induct) auto

lemma lsum_0I: \<open>\<forall>x\<in>lset lxs. x = 0 \<Longrightarrow> lsum lxs = 0\<close>
  by (subst lsum_code_alt) auto

lemma lsum_0_iff: \<open>lsum lxs = 0 \<longleftrightarrow> (\<forall>x \<in> lset lxs. x = 0)\<close>
  by (metis lsum_0I lsum_0D)

lemma lsum_lappend_lfinite: \<open>lfinite lxs \<Longrightarrow> lsum (lappend lxs lys) = lsum lxs + lsum lys\<close>
  by (induct lxs rule: lfinite.induct) auto

lemma lsum_lappend: \<open>lsum (lappend lxs lys) = (if lfinite lxs then lsum lxs + lsum lys else lsum lxs)\<close>
  by (auto simp: lappend_inf lsum_lappend_lfinite)

lemma lsum_llist_of[simp]: \<open>lsum (llist_of xs) = sum_list xs\<close>
  by (induct xs) auto

lemma lsum_cont:
  \<open>Complete_Partial_Order.chain lprefix Y \<Longrightarrow> Y \<noteq> {} \<Longrightarrow> lsum (lSup Y) = \<Squnion> (lsum ` Y)\<close>
proof (coinduction arbitrary: Y rule: enat_coinduct)
  case Eq_enat
  then show ?case
  proof (intro allI impI conjI disjI1)
    show \<open>Complete_Partial_Order.chain lprefix Y \<Longrightarrow> Y \<noteq> {} \<Longrightarrow> (lsum (lSup Y) = 0) = (\<Squnion> (lsum ` Y) = 0)\<close>
      by (simp add: Sup_eq_0_iff lset_lSup lsum_0_iff)
  next
    assume hn0_lsum: \<open>lsum (lSup Y) \<noteq> 0\<close> and hn0_Sup: \<open>\<Squnion> (lsum ` Y) \<noteq> 0\<close>
    show \<open>(\<exists>Y'. epred (lsum (lSup Y)) = lsum (lSup Y') \<and> epred (\<Squnion> (lsum ` Y)) = \<Squnion> (lsum ` Y') \<and>
                Complete_Partial_Order.chain lprefix Y' \<and> Y' \<noteq> {})\<close>
    proof -
      have lnth_eq_Y: \<open>lnth lxs i = lnth lys i\<close>
        if \<open>enat i < llength lxs\<close> \<open>lxs \<in> Y\<close> \<open>enat i < llength lys\<close> \<open>lys \<in> Y\<close> for lxs lys i
        using Eq_enat(1) that by (force simp: chain_def dest: lprefix_lnthD[of _ _ i])
      obtain lys z where hlys: \<open>lys \<in> Y\<close> and hz: \<open>z \<in> lset lys\<close> \<open>z \<noteq> 0\<close>
        using hn0_lsum Eq_enat(1) by (auto simp: lsum_0_iff lset_lSup)
      define A where \<open>A = {i. \<forall>lys \<in> Y. ltaken i lys = replicate (case llength lys of enat j \<Rightarrow> min i j | _ \<Rightarrow> i) 0}\<close>
      define i where \<open>i = Max A\<close>
      have ne: \<open>A \<noteq> {}\<close>
        using Eq_enat(2) \<open>lys \<in> Y\<close> by (auto simp: A_def enat_0 intro!: exI[of _ 0] split: enat.splits)
      have fin: \<open>finite A\<close>
      proof -
        from hn0_lsum Eq_enat(1) obtain lys' where hlys': \<open>lys' \<in> Y\<close> and hn0: \<open>lsum lys' \<noteq> 0\<close>
          by (auto simp: lset_lSup lsum_0_iff)
        from hn0 obtain n where hn: \<open>enat n < llength lys'\<close> \<open>lnth lys' n \<noteq> 0\<close>
          by (auto simp: lsum_0_iff in_lset_conv_lnth dest: lsum_0D)
        show \<open>finite A\<close>
        proof (rule finite_subset[of _ \<open>{0..n}\<close>])
          show \<open>A \<subseteq> {0..n}\<close>
          proof
            fix k assume hk: \<open>k \<in> A\<close>
            have hkprop: \<open>ltaken k lys' = replicate (case llength lys' of enat j \<Rightarrow> min k j | _ \<Rightarrow> k) 0\<close>
              using hk hlys' by (auto simp: A_def)
            have \<open>n < k \<Longrightarrow> False\<close>
            proof -
              assume hnk: \<open>n < k\<close>
              have \<open>nth (ltaken k lys') n = lnth lys' n\<close>
              proof (cases \<open>enat k \<le> llength lys'\<close>)
                case True
                thus ?thesis using hnk by (simp add: nth_ltaken)
              next
                case False
                hence hlt: \<open>llength lys' < enat k\<close> by simp
                then obtain m where hm: \<open>llength lys' = enat m\<close>
                  by (cases \<open>llength lys'\<close>) (auto simp: enat_def)
                have hmk: \<open>m \<le> k\<close> using hlt hm by auto
                have hnm: \<open>n < m\<close> using hn(1) hm by auto
                have \<open>ltaken k lys' = ltaken m lys'\<close>
                  by (rule ltaken_all_same) (simp_all add: hm hmk)
                thus ?thesis using hnm hm by (simp add: nth_ltaken)
              qed
              moreover have \<open>nth (replicate (case llength lys' of enat j \<Rightarrow> min k j | _ \<Rightarrow> k) 0) n = 0\<close>
                using hn(1) hnk by (auto simp: min_def split: enat.splits)
              ultimately show False using hkprop hn(2) by metis
            qed
            thus \<open>k \<in> {0..n}\<close> by (force simp: not_less)
          qed
        qed simp
      qed
      have iA: \<open>\<forall>lys \<in> Y. ltaken i lys = replicate (case llength lys of enat j \<Rightarrow> min i j | _ \<Rightarrow> i) 0\<close>
        using Max_in[OF fin ne] unfolding i_def A_def by blast
      from iA[THEN bspec, of lys] hlys \<open>z \<in> lset lys\<close> \<open>z \<noteq> 0\<close> have hi: \<open>enat i < llength lys\<close>
      proof -
        have hiA: \<open>ltaken i lys = replicate (case llength lys of enat j \<Rightarrow> min i j | _ \<Rightarrow> i) 0\<close>
          using iA hlys by blast
        obtain n0 where hn0_len: \<open>enat n0 < llength lys\<close> and hn0_nth: \<open>lnth lys n0 = z\<close>
          using \<open>z \<in> lset lys\<close> by (auto simp: in_lset_conv_lnth)
        show \<open>enat i < llength lys\<close>
        proof (rule ccontr)
          assume h: \<open>\<not> enat i < llength lys\<close>
          hence hfin: \<open>llength lys \<noteq> \<infinity>\<close> by (cases \<open>llength lys\<close>) auto
          then obtain m where hm: \<open>llength lys = enat m\<close> by (cases \<open>llength lys\<close>) auto
          from h hm have him: \<open>m \<le> i\<close> by auto
          have hn0m: \<open>n0 < m\<close> using hn0_len hm by auto
          have \<open>nth (ltaken i lys) n0 = lnth lys n0\<close>
          proof (cases \<open>enat i \<le> llength lys\<close>)
            case True
            thus ?thesis using hn0m him hm by (simp add: nth_ltaken)
          next
            case False
            hence \<open>ltaken i lys = ltaken m lys\<close>
              by (rule_tac ltaken_all_same) (simp_all add: hm him)
            thus ?thesis using hn0m hm by (simp add: nth_ltaken)
          qed
          moreover have \<open>nth (ltaken i lys) n0 = 0\<close>
            using hiA hm him hn0m by (auto simp: min_def)
          ultimately show False using hn0_nth \<open>z \<noteq> 0\<close> by auto
        qed
      qed
      with iA hlys have hpref: \<open>lprefix (llist_of (replicate i 0)) lys\<close>
        by (metis length_ltaken length_replicate lprefix_conv_lappend ltaken_ldropn_decomp nless_le)
      obtain n where hn: \<open>\<forall>lys \<in> Y. enat i \<ge> llength lys \<or> lnth lys i = n\<close>
        using lnth_eq_Y by (meson linorder_not_le)
      have hn0: \<open>n = 0 \<Longrightarrow> Suc i \<in> A\<close>
      proof -
        assume hn0_eq: \<open>n = 0\<close>
        show \<open>Suc i \<in> A\<close>
          unfolding A_def mem_Collect_eq
        proof
          fix lys' assume hlys'_Y: \<open>lys' \<in> Y\<close>
          show \<open>ltaken (Suc i) lys' = replicate (case llength lys' of enat j \<Rightarrow> min (Suc i) j | _ \<Rightarrow> Suc i) 0\<close>
          proof (cases \<open>enat i < llength lys'\<close>)
            case True
            hence hstep: \<open>ltaken (Suc i) lys' = ltaken i lys' @ [lnth lys' i]\<close>
              by (metis ltaken_Suc)
            have \<open>lnth lys' i = 0\<close>
              using hn hlys'_Y hn0_eq True by auto
            moreover have \<open>ltaken i lys' = replicate (case llength lys' of enat j \<Rightarrow> min i j | _ \<Rightarrow> i) 0\<close>
              using iA hlys'_Y by blast
            ultimately show ?thesis
              using hstep \<open>enat i < llength lys'\<close>
              by (subst hstep, auto simp: min_def replicate_append_same Suc_ile_eq split: enat.splits)
          next
            case False
            hence \<open>ltaken (Suc i) lys' = ltaken i lys'\<close>
              by (metis ltaken_Suc)
            moreover have \<open>ltaken i lys' = replicate (case llength lys' of enat j \<Rightarrow> min i j | _ \<Rightarrow> i) 0\<close>
              using iA hlys'_Y by blast
            ultimately show ?thesis
              using False
              by (auto simp: min_def not_less split: enat.splits)
          qed
        qed
      qed
      have hnn: \<open>n \<noteq> 0\<close>
        using Max_eq_iff[OF fin ne, of i, THEN iffD1, OF i_def[symmetric], THEN conjunct2, rule_format, of \<open>Suc i\<close>]
          hn0 by fastforce
      have ldropn_cases: \<open>lys = LNil \<or> (\<exists>lys'. lys = LCons n lys')\<close>
        if \<open>lys \<in> ldropn i ` Y\<close> for lys
        using that hn
        by (metis (mono_tags, lifting) image_iff ldropn_Suc_conv_ldropn ldropn_eq_LNil linorder_not_le)
      have hTHE: \<open>(THE x. x \<in> lhd ` (ldropn i ` Y \<inter> {xs. \<not> lnull xs})) = n\<close>
      proof (intro the_equality)
        show \<open>n \<in> lhd ` (ldropn i ` Y \<inter> {xs. \<not> lnull xs})\<close>
          by (metis IntI hi hlys image_eqI ldropn_Suc_conv_ldropn lhd_LCons linorder_not_le
              llist.disc(2) mem_Collect_eq hn)
        show \<open>\<And>x. x \<in> lhd ` (ldropn i ` Y \<inter> {xs. \<not> lnull xs}) \<Longrightarrow> x = n\<close>
        proof -
          fix x assume \<open>x \<in> lhd ` (ldropn i ` Y \<inter> {xs. \<not> lnull xs})\<close>
          then obtain lxs where hlxs: \<open>lxs \<in> Y\<close> \<open>\<not> lnull (ldropn i lxs)\<close> \<open>x = lhd (ldropn i lxs)\<close>
            by auto
          from hlxs(2) have hlen: \<open>enat i < llength lxs\<close>
            by (simp add: lnull_def ldropn_eq_LNil not_less)
          from hlxs(3) have \<open>x = lnth lxs i\<close>
            by (simp add: lhd_ldropn hlen)
          with hn hlxs(1) hlen show \<open>x = n\<close>
            by auto
        qed
      qed
      have hLCons: \<open>(\<lambda>x. LCons (epred n) (ltl x)) ` X \<inter> {xs. \<not> lnull xs} =
            (\<lambda>x. LCons (epred n) (ltl x)) ` X\<close> for X
        by auto
      have h4: \<open>ldropn i lys \<in> ldropn i ` Y \<inter> {xs. \<not> lnull xs}\<close>
        using hi hlys by auto
      define Y' where \<open>Y' = (LCons (epred n) \<circ> ltl) ` (ldropn i ` Y \<inter> {xs. \<not> lnull xs})\<close>
      show ?thesis
      proof (intro disjI1 exI[of _ Y'] conjI)
        show \<open>Y' \<noteq> {}\<close>
          unfolding Y'_def using h4 by force
      next
        show \<open>Complete_Partial_Order.chain lprefix Y'\<close>
          unfolding Y'_def chain_def
        proof (intro ballI)
          fix lxs' lys'
          assume hm1: \<open>lxs' \<in> (LCons (epred n) \<circ> ltl) ` (ldropn i ` Y \<inter> {xs. \<not> lnull xs})\<close>
            and hm2: \<open>lys' \<in> (LCons (epred n) \<circ> ltl) ` (ldropn i ` Y \<inter> {xs. \<not> lnull xs})\<close>
          from hm1 obtain lxs0 where hlxs0: \<open>lxs0 \<in> ldropn i ` Y\<close> \<open>\<not> lnull lxs0\<close>
            \<open>lxs' = LCons (epred n) (ltl lxs0)\<close> by auto
          from hm2 obtain lys0 where hlys0: \<open>lys0 \<in> ldropn i ` Y\<close> \<open>\<not> lnull lys0\<close>
            \<open>lys' = LCons (epred n) (ltl lys0)\<close> by auto
          from hlxs0(1) obtain lxs1 where hlxs1: \<open>lxs1 \<in> Y\<close> \<open>lxs0 = ldropn i lxs1\<close> by auto
          from hlys0(1) obtain lys1 where hlys1: \<open>lys1 \<in> Y\<close> \<open>lys0 = ldropn i lys1\<close> by auto
          from Eq_enat(1) hlxs1(1) hlys1(1) have \<open>lprefix lxs1 lys1 \<or> lprefix lys1 lxs1\<close>
            by (auto simp: chain_def)
          thus \<open>lprefix lxs' lys' \<or> lprefix lys' lxs'\<close>
            using hlxs0(3) hlys0(3) hlxs1(2) hlys1(2)
            by (auto intro: lprefix_ltlI monotone_ldropn'[THEN monotoneD])
        qed
      next
        let ?S = \<open>ldropn i ` Y \<inter> {xs. \<not> lnull xs}\<close>
        have hS_ne: \<open>?S \<noteq> {}\<close> using h4 by force
        have lSup_ldropn: \<open>lSup (ldropn i ` Y) = LCons n (lSup (ltl ` ?S))\<close>
        proof (subst lSup.code, auto simp: hTHE h4)
          show \<open>\<exists>x\<in>Y. \<not> llength x \<le> enat i\<close>
            using hlys hi by (intro bexI[OF _ hlys]) auto
        qed
        have lSup_Y': \<open>lSup Y' = LCons (epred n) (lSup (ltl ` ?S))\<close>
        proof -
          have hne: \<open>ltl ` ?S \<noteq> {}\<close> using hS_ne by auto
          have \<open>Y' = LCons (epred n) ` ltl ` ?S\<close>
            by (simp add: Y'_def image_image)
          thus ?thesis using hne by (simp add: lSup_LCons)
        qed
        have lSup_Y_eq: \<open>lSup Y = lappend (llist_of (replicate i 0)) (lSup (ldropn i ` Y))\<close>
          using lSup_eq_lappend[OF Eq_enat(1), of \<open>replicate i 0\<close>] hlys hpref by auto
        show \<open>epred (lsum (lSup Y)) = lsum (lSup Y')\<close>
          using lSup_Y_eq lSup_ldropn lSup_Y' hnn
          by (simp add: lsum_lappend sum_list_replicate epred_iadd1)
      next
        let ?S = \<open>ldropn i ` Y \<inter> {xs. \<not> lnull xs}\<close>
        have hS_ne: \<open>?S \<noteq> {}\<close> using h4 by force
        have lSup_Y': \<open>lSup Y' = LCons (epred n) (lSup (ltl ` ?S))\<close>
        proof -
          have hne: \<open>ltl ` ?S \<noteq> {}\<close> using hS_ne by auto
          have \<open>Y' = LCons (epred n) ` ltl ` ?S\<close>
            by (simp add: Y'_def image_image)
          thus ?thesis using hne by (simp add: lSup_LCons)
        qed
        have lsum_lzs: \<open>lsum lzs = lsum (ldropn i lzs)\<close> if \<open>lzs \<in> Y\<close> for lzs
          using iA[rule_format, OF that]
          by (subst ltaken_ldropn_decomp[of _ i]) (auto simp: lsum_lappend)
        have lsum_eq_sets: \<open>(epred \<circ> lsum) ` (Y \<inter> {lzs. lsum lzs \<noteq> 0}) =
                            lsum ` Y'\<close>
        proof (rule set_eqI)
          fix v
          show \<open>v \<in> (epred \<circ> lsum) ` (Y \<inter> {lzs. lsum lzs \<noteq> 0}) \<longleftrightarrow> v \<in> lsum ` Y'\<close>
          proof
            assume \<open>v \<in> (epred \<circ> lsum) ` (Y \<inter> {lzs. lsum lzs \<noteq> 0})\<close>
            then obtain lzs where hlzs: \<open>lzs \<in> Y\<close> \<open>lsum lzs \<noteq> 0\<close> \<open>v = epred (lsum lzs)\<close> by auto
            have hnd: \<open>ldropn i lzs \<noteq> LNil\<close>
              using hlzs(1,2) lsum_lzs by (auto simp: lsum_0_iff)
            then obtain lzs' where hlzs': \<open>ldropn i lzs = LCons n lzs'\<close>
              using ldropn_cases[of \<open>ldropn i lzs\<close>] hlzs(1) by auto
            have \<open>LCons (epred n) (ltl (ldropn i lzs)) \<in> Y'\<close>
              using hlzs(1) hnd by (auto simp: Y'_def)
            moreover have \<open>v = lsum (LCons (epred n) (ltl (ldropn i lzs)))\<close>
              using hlzs(3) hlzs'(1) lsum_lzs[OF hlzs(1)] hnn
              by (simp add: epred_iadd1)
            ultimately show \<open>v \<in> lsum ` Y'\<close>
              by blast
          next
            assume \<open>v \<in> lsum ` Y'\<close>
            then obtain ya where hya: \<open>ya \<in> Y'\<close> \<open>v = lsum ya\<close> by auto
            from hya(1) obtain lzs where hlzs: \<open>lzs \<in> Y\<close> \<open>ldropn i lzs \<in> ?S\<close>
              \<open>ya = LCons (epred n) (ltl (ldropn i lzs))\<close> by (auto simp: Y'_def)
            from hlzs(2) have hnd: \<open>\<not> lnull (ldropn i lzs)\<close> by auto
            then obtain lzs' where hlzs': \<open>ldropn i lzs = LCons n lzs'\<close>
              using ldropn_cases[of \<open>ldropn i lzs\<close>] hlzs(1) by fastforce
            have \<open>lsum lzs = n + lsum lzs'\<close>
              using lsum_lzs[OF hlzs(1)] hlzs' by simp
            hence \<open>lsum lzs \<noteq> 0\<close> using hnn by auto
            moreover have \<open>v = epred (lsum lzs)\<close>
              using hya(2) hlzs(3) hlzs' lsum_lzs[OF hlzs(1)] hnn
              by (simp add: epred_iadd1)
            ultimately show \<open>v \<in> (epred \<circ> lsum) ` (Y \<inter> {lzs. lsum lzs \<noteq> 0})\<close>
              using hlzs(1) by auto
          qed
        qed
        show \<open>epred (\<Squnion> (lsum ` Y)) = \<Squnion> (lsum ` Y')\<close>
        proof -
          have \<open>\<Squnion> (lsum ` Y) = \<Squnion> (lsum ` (Y \<inter> {lzs. lsum lzs \<noteq> 0}))\<close>
            using hlys hz(1,2)
            by (subst Sup_enat_remove0) (auto dest: lsum_0D intro!: arg_cong[where f=Sup])
          moreover have \<open>epred (\<Squnion> (lsum ` (Y \<inter> {lzs. lsum lzs \<noteq> 0}))) =
                         \<Squnion> (epred ` (lsum ` (Y \<inter> {lzs. lsum lzs \<noteq> 0})))\<close>
            by (rule epred_Sup)
          moreover have \<open>epred ` (lsum ` (Y \<inter> {lzs. lsum lzs \<noteq> 0})) =
                         (epred \<circ> lsum) ` (Y \<inter> {lzs. lsum lzs \<noteq> 0})\<close>
            by (simp add: image_image)
          ultimately show ?thesis
            using lsum_eq_sets by simp
        qed
      qed
    qed
  qed
qed

lemma mcont2mcont_lsum[THEN lfp.mcont2mcont, simp, cont_intro]:
  shows mcont_lsum: \<open>mcont lSup (lprefix) Sup (\<le>) lsum\<close>
  by (auto simp: mcont_def monotone_def lsum_mono cont_def lsum_cont)


lemma lsum_lfilter_nonzero: \<open>lsum (lfilter ((\<noteq>) 0) lxs) = lsum lxs\<close>
  by (induct lxs) auto

abbreviation \<open>LSUM lxs f \<equiv> lsum (lmap f lxs)\<close>

abbreviation \<open>lenats \<equiv> lupt 0 \<infinity>\<close>

lemma LSUM_lfilter: \<open>LSUM (lfilter (\<lambda>x. f x \<noteq> 0) lxs) f = LSUM lxs f\<close>
  by (induct lxs) auto

lemma LSUM_count_llist_lfilter:
  \<open>lsum (lmap (\<lambda>lxs. count_llist lxs x) (lfilter (\<lambda>x. \<not> lnull x) lxss)) =
  lsum (lmap (\<lambda>lxs. count_llist lxs x) lxss)\<close>
proof (induct lxss)
  case LNil
  then show ?case by (auto simp: count_llist_zero_iff)
next
  case (LCons lxs lxss)
  then show ?case by (auto simp: count_llist_zero_iff, metis lnull_def empty_iff lset_LNil)
qed simp

lemma lflat_LNil[simp]: \<open>lflat LNil = LNil\<close>
  by (subst lflat.simps) auto

lemma lflat_LCons[simp]: \<open>lflat (LCons xs lxss) = lappend (llist_of xs) (lflat lxss)\<close>
  by (subst lflat.simps) auto

lemma count_llist_mono:
  assumes \<open>lprefix lxs lys\<close>
  shows \<open>count_llist lxs x \<le> count_llist lys x\<close>
proof (cases \<open>lfinite lxs\<close>)
  case True
  then show ?thesis using assms
    by (induct lxs arbitrary: lys pred: lfinite) (auto simp: LCons_lprefix_conv)
next
  case False
  then show ?thesis using assms
    by (simp add: not_lfinite_lprefix_conv_eq)
qed

lemma ldropWhile_not_lnull_alt:
  \<open>ldropWhile ((\<noteq>) x) ` Y \<inter> {lxs. \<not> lnull lxs} = ldropWhile ((\<noteq>) x) ` {lxs \<in> Y. x \<in> lset lxs}\<close>
  by auto

lemma count_llist_cont: \<open>Complete_Partial_Order.chain lprefix Y \<Longrightarrow> Y \<noteq> {} \<Longrightarrow>
  count_llist (lSup Y) x = (\<Squnion>lxs\<in>Y. count_llist lxs x)\<close>
proof (coinduction arbitrary: Y)
  case (eq_enat Y)
  then have chain_Y: \<open>Complete_Partial_Order.chain lprefix Y\<close> and ne_Y: \<open>Y \<noteq> {}\<close> by auto
  show ?case
  proof (rule conjI)
    from chain_Y ne_Y show \<open>(count_llist (lSup Y) x = 0) = ((\<Squnion>lxs\<in>Y. count_llist lxs x) = 0)\<close>
      by (auto simp: count_llist_zero_iff Sup_eq_0_iff lset_lSup)
  next
    show \<open>count_llist (lSup Y) x \<noteq> 0 \<longrightarrow> (\<Squnion>lxs\<in>Y. count_llist lxs x) \<noteq> 0 \<longrightarrow>
      (\<exists>Z. epred (count_llist (lSup Y) x) = count_llist (lSup Z) x \<and>
            epred (\<Squnion>lxs\<in>Y. count_llist lxs x) = (\<Squnion>lxs\<in>Z. count_llist lxs x) \<and>
            Complete_Partial_Order.chain lprefix Z \<and> Z \<noteq> {}) \<or>
      epred (count_llist (lSup Y) x) = epred (\<Squnion>lxs\<in>Y. count_llist lxs x)\<close>
    proof (intro impI disjI1)
      assume h1: \<open>count_llist (lSup Y) x \<noteq> 0\<close> and h2: \<open>(\<Squnion>lxs\<in>Y. count_llist lxs x) \<noteq> 0\<close>
      define Z where \<open>Z \<equiv> ltl ` (ldropWhile ((\<noteq>) x) ` Y \<inter> {lxs. \<not> lnull lxs})\<close>
      have chain_Z: \<open>Complete_Partial_Order.chain lprefix Z\<close>
        unfolding Z_def using chain_Y
        by (auto simp: chain_def ldropWhile_not_lnull_alt
            intro!: lprefix_ltlI mcont_monoD[OF mcont_ldropWhile])
      have ne_Yx: \<open>{lxs\<in>Y. x\<in>lset lxs} \<noteq> {}\<close>
        using chain_Y ne_Y h1 by (auto simp: lset_lSup count_llist_zero_iff)
      have ne_Z: \<open>Z \<noteq> {}\<close>
        unfolding Z_def
        using ne_Yx by (auto simp: ldropWhile_not_lnull_alt)
      have x_lset: \<open>x \<in> lset (lSup Y)\<close>
        using h1 by (simp add: count_llist_zero_iff)
      have drop_cont: \<open>ldropWhile ((\<noteq>) x) (lSup Y) = lSup (ldropWhile ((\<noteq>) x) ` Y)\<close>
        using chain_Y ne_Y by (rule mcont_contD[OF mcont_ldropWhile])
      have eq1: \<open>epred (count_llist (lSup Y) x) = count_llist (lSup Z) x\<close>
      proof -
        have \<open>epred (count_llist (lSup Y) x) = count_llist (ltl (ldropWhile ((\<noteq>) x) (lSup Y))) x\<close>
          using x_lset by (rule count_llist_sel)
        also have \<open>ltl (ldropWhile ((\<noteq>) x) (lSup Y)) = lSup Z\<close>
          by (simp add: drop_cont image_image Z_def)
        finally show ?thesis .
      qed
      have eq2: \<open>epred (\<Squnion>lxs\<in>Y. count_llist lxs x) = (\<Squnion>lxs\<in>Z. count_llist lxs x)\<close>
      proof -
        have aux: \<open>(\<Squnion>lxs\<in>Y. epred (count_llist lxs x)) = (\<Squnion>lxs\<in>{lxs\<in>Y. x\<in>lset lxs}. count_llist (ltl (ldropWhile ((\<noteq>) x) lxs)) x)\<close>
        proof (rule antisym)
          show \<open>(\<Squnion>lxs\<in>Y. epred (count_llist lxs x)) \<le> (\<Squnion>lxs\<in>{lxs\<in>Y. x\<in>lset lxs}. count_llist (ltl (ldropWhile ((\<noteq>) x) lxs)) x)\<close>
          proof (rule cSUP_mono[OF ne_Y])
            show \<open>bdd_above ((\<lambda>lxs. count_llist (ltl (ldropWhile ((\<noteq>) x) lxs)) x) ` {lxs\<in>Y. x\<in>lset lxs})\<close>
              by (auto simp: bdd_above_def)
            fix lxs assume lxs_Y: \<open>lxs \<in> Y\<close>
            show \<open>\<exists>ya \<in> {lxs\<in>Y. x\<in>lset lxs}. epred (count_llist lxs x) \<le> count_llist (ltl (ldropWhile ((\<noteq>) x) ya)) x\<close>
            proof (cases \<open>x \<in> lset lxs\<close>)
              case True
              with lxs_Y show ?thesis by auto
            next
              case False
              with ne_Yx obtain ya where ya_Y: \<open>ya \<in> Y\<close> and x_ya: \<open>x \<in> lset ya\<close> by blast
              from False have \<open>count_llist lxs x = 0\<close> by (simp add: count_llist_zero_iff)
              then show ?thesis using ya_Y x_ya by auto
            qed
          qed
          show \<open>(\<Squnion>lxs\<in>{lxs\<in>Y. x\<in>lset lxs}. count_llist (ltl (ldropWhile ((\<noteq>) x) lxs)) x) \<le> (\<Squnion>lxs\<in>Y. epred (count_llist lxs x))\<close>
          proof (rule cSUP_mono[OF ne_Yx])
            show \<open>bdd_above ((\<lambda>lxs. epred (count_llist lxs x)) ` Y)\<close>
              by (auto simp: bdd_above_def)
            fix lxs assume \<open>lxs \<in> {lxs\<in>Y. x\<in>lset lxs}\<close>
            then have lxs_Y: \<open>lxs \<in> Y\<close> and x_lxs: \<open>x \<in> lset lxs\<close> by auto
            show \<open>\<exists>m \<in> Y. count_llist (ltl (ldropWhile ((\<noteq>) x) lxs)) x \<le> epred (count_llist m x)\<close>
              using lxs_Y x_lxs
              by (auto intro!: bexI[of _ lxs])
          qed
        qed
        then show ?thesis
          by (simp add: epred_Sup image_image ldropWhile_not_lnull_alt Z_def)
      qed
      show \<open>\<exists>Z. epred (count_llist (lSup Y) x) = count_llist (lSup Z) x \<and>
            epred (\<Squnion>lxs\<in>Y. count_llist lxs x) = (\<Squnion>lxs\<in>Z. count_llist lxs x) \<and>
            Complete_Partial_Order.chain lprefix Z \<and> Z \<noteq> {}\<close>
        by (rule exI[of _ Z]) (use eq1 eq2 chain_Z ne_Z in simp)
    qed
  qed
qed

lemma mcont2mcont_count_llist[THEN lfp.mcont2mcont, simp, cont_intro]:
  shows mcont_count_llist: \<open>mcont lSup (lprefix) Sup (\<le>) (\<lambda>lxs. count_llist lxs x)\<close>
  by (auto simp: mcont_def cont_def monotone_def count_llist_mono count_llist_cont)

lemma mono2mono_lflat[THEN llist.mono2mono, simp, cont_intro]:
  shows mono_lflat: \<open>monotone lprefix lprefix lflat\<close>
  by (rule llist.fixp_preserves_mono1[OF lflat.mono lflat_def]) simp

lemma mcont2mcont_lflat[THEN llist.mcont2mcont, simp, cont_intro]:
  shows mcont_lflat: \<open>mcont lSup lprefix lSup lprefix lflat\<close>
  by (rule llist.fixp_preserves_mcont1[OF lflat.mono lflat_def]) simp

lemma lflat_LNil_iff: \<open>lflat lxss = LNil \<longleftrightarrow> (\<forall>xs \<in> lset lxss. xs = [])\<close>
  by (induct lxss) (auto simp: llist_of_eq_LNil_conv lappend_eq_LNil_iff)

lemma count_llist_lflat: \<open>count_llist (lflat lxss) x = lsum (lmap (\<lambda>xs. count_list xs x) lxss)\<close>
  by (induct lxss) (auto simp: count_llist_lappend)

lemma lset_lflat: \<open>lset (lflat lxss) = (\<Union>xs \<in> lset lxss. set xs)\<close>
  unfolding in_lset_iff_count_llist set_eq_iff
  by (auto simp: count_llist_zero_iff count_llist_lflat lsum_0_iff count_list_0_iff enat_0_iff)

definition \<open>lvertical lxss i = (if enat i < llength lxss then ltaken (Suc i) (lnth lxss i) else [])\<close>
definition \<open>lhorizontal lxss j = List.map_filter (\<lambda>lxs. if enat j < llength lxs then Some (lnth lxs j) else None) (ltaken j lxss)\<close>
definition lmerge where
  \<open>lmerge lxss = lflat (lmap (\<lambda>i. lvertical lxss i @ lhorizontal lxss i) (lupt 0 \<infinity>))\<close>

lemma set_ltaken_conv': \<open>set (ltaken n lxs) = (case llength lxs of enat m \<Rightarrow> lnth lxs ` {0..<min n m} | _ \<Rightarrow> lnth lxs ` {0 ..< n})\<close>
proof -
  show ?thesis
  proof -
    { fix m x
      assume \<open>m < n\<close> \<open>llength lxs = enat m\<close> \<open>x \<in> set (ltaken n lxs)\<close>
      then have \<open>x \<in> lnth lxs ` {0..<m}\<close>
        by (metis enat_ord_simps(1) linorder_not_le ltaken_all_same nle_le set_ltaken_conv)
    }
    moreover
    { fix m l
      assume \<open>m < n\<close> \<open>llength lxs = enat m\<close> \<open>l < m\<close>
      then have \<open>lnth lxs l \<in> set (ltaken n lxs)\<close>
        by (metis enat_ord_simps(2) in_lset_conv_lnth ltaken_ldropn_decomp linorder_not_le
              lset_llist_of order_le_less ldropn_eq_LNil lappend_LNil2)
    }
    ultimately show ?thesis
      by (auto simp: set_ltaken_conv min_def not_le split: enat.splits)
  qed
qed

lemma lset_lmerge: \<open>lset (lmerge lxss) = (\<Union>lxs \<in> lset lxss. lset lxs)\<close>
proof safe
  fix x
  assume \<open>x \<in> lset (lmerge lxss)\<close>
  then show \<open>x \<in> \<Union> (lset ` lset lxss)\<close>
  proof -
    have vert: \<open>\<And>i. set (lvertical lxss i) \<subseteq> \<Union> (lset ` lset lxss)\<close>
    proof
      fix i y assume hy: \<open>y \<in> set (lvertical lxss i)\<close>
      show \<open>y \<in> \<Union> (lset ` lset lxss)\<close>
      proof (cases \<open>enat i < llength lxss\<close>)
        case True
        have hsub: \<open>set (lvertical lxss i) \<subseteq> lset (lnth lxss i)\<close>
          using True set_ltaken[of \<open>Suc i\<close> \<open>lnth lxss i\<close>]
          by (auto simp: lvertical_def intro: lset_intros dest: set_mp[OF set_ltaken])
        have hmem: \<open>lnth lxss i \<in> lset lxss\<close>
          using True by (auto simp: in_lset_conv_lnth)
        show ?thesis using hy hsub hmem by blast
      next
        case False
        then have \<open>set (lvertical lxss i) = {}\<close> by (simp add: lvertical_def)
        then show ?thesis using hy by simp
      qed
    qed
    have horiz: \<open>\<And>j. set (lhorizontal lxss j) \<subseteq> \<Union> (lset ` lset lxss)\<close>
    proof
      fix j y assume hy: \<open>y \<in> set (lhorizontal lxss j)\<close>
      then obtain n where hn: \<open>enat n < llength lxss\<close> and hjn: \<open>enat j < llength (lnth lxss n)\<close>
          and yj: \<open>y = lnth (lnth lxss n) j\<close>
        by (auto simp: lhorizontal_def map_filter_def in_lset_conv_lnth not_less not_le
            enat_0_iff min_def split: enat.splits if_splits dest!: set_mp[OF set_ltaken])
      have hmem: \<open>lnth lxss n \<in> lset lxss\<close>
        using hn by (auto simp: in_lset_conv_lnth)
      have hin: \<open>y \<in> lset (lnth lxss n)\<close>
        using hjn yj by (auto simp: in_lset_conv_lnth)
      show \<open>y \<in> \<Union> (lset ` lset lxss)\<close>
        using hmem hin by blast
    qed
    from \<open>x \<in> lset (lmerge lxss)\<close>
    obtain i where \<open>x \<in> set (lvertical lxss i) \<or> x \<in> set (lhorizontal lxss i)\<close>
      unfolding lmerge_def lset_lflat
      by (auto simp: lset_lupt)
    then show ?thesis
      using vert horiz by blast
  qed
next
  fix x lxs
  assume xlxss: \<open>lxs \<in> lset lxss\<close> and xlxs: \<open>x \<in> lset lxs\<close>
  from xlxss obtain i where hi: \<open>enat i < llength lxss\<close> and lxi: \<open>lnth lxss i = lxs\<close>
    by (auto simp: in_lset_conv_lnth)
  from xlxs obtain j where hj: \<open>enat j < llength lxs\<close> and xj: \<open>lnth lxs j = x\<close>
    by (auto simp: in_lset_conv_lnth)
  show \<open>x \<in> lset (lmerge lxss)\<close>
  proof (cases \<open>j \<le> i\<close>)
    case jle: True
    have x_in_vert: \<open>x \<in> set (lvertical lxss i)\<close>
    proof (cases \<open>enat (Suc i) \<le> llength lxs\<close>)
      case leq: True
      have ji_lt: \<open>j < Suc i\<close> using le_imp_less_Suc jle by blast
      have nth_eq: \<open>ltaken (Suc i) lxs ! j = lnth lxs j\<close>
        by (rule nth_ltaken) (fact ji_lt, fact leq)
      have jlt: \<open>j < length (ltaken (Suc i) lxs)\<close>
        using leq ji_lt by (metis length_ltaken)
      show ?thesis
        using hi hj xj lxi nth_eq jlt
        by (auto simp: lvertical_def in_set_conv_nth simp del: ltaken.simps)
    next
      case nleq: False
      obtain k where fin: \<open>llength lxs = enat k\<close>
        by (meson less_enatE linorder_not_le nleq)
      have len_eq: \<open>length (ltaken (Suc i) lxs) = k\<close>
        using nleq fin by (metis length_ltaken the_enat.simps)
      have jltk: \<open>j < k\<close>
        using hj fin by simp
      have nth_eq: \<open>ltaken (Suc i) lxs ! j = lnth lxs j\<close>
        by (metis len_eq jltk lnth_lappend_llist_of ltaken_ldropn_decomp)
      show ?thesis
        using hi hj xj lxi nth_eq jltk len_eq
        by (auto simp: lvertical_def in_set_conv_nth simp del: ltaken.simps)
    qed
    show ?thesis
      unfolding lmerge_def lset_lflat
      using x_in_vert by (auto simp: lset_lupt)
  next
    case False
    have x_in_horiz: \<open>x \<in> set (lhorizontal lxss j)\<close>
      using hi hj xj lxi False
      by (auto simp: not_le lhorizontal_def map_filter_def set_ltaken_conv' split: enat.splits)
    show ?thesis
      unfolding lmerge_def lset_lflat
      using x_in_horiz by (auto simp: lset_lupt)
  qed
qed

lemma lsum_lmap_add: \<open>lsum (lmap (\<lambda>x. f x + g x) lxs) = lsum (lmap f lxs) + lsum (lmap g lxs)\<close>
  by (induct lxs) auto

lemma count_list_alt: \<open>count_list xs x = card {j. j < length xs \<and> xs ! j = x}\<close>
proof (induct xs)
  case (Cons a xs)
  then show ?case
  proof (cases \<open>a = x\<close>)
    case True
    with Cons show ?thesis
    proof -
      have eq: \<open>{j. j < Suc (length xs) \<and> (x # xs) ! j = x} = insert 0 (Suc ` {j. j < length xs \<and> xs ! j = x})\<close>
        by (auto simp: nth_Cons' less_Suc_eq_0_disj)
      have fin: \<open>finite {j. j < length xs \<and> xs ! j = x}\<close> by simp
      have notin: \<open>0 \<notin> Suc ` {j. j < length xs \<and> xs ! j = x}\<close> by simp
      have inj: \<open>inj_on Suc {j. j < length xs \<and> xs ! j = x}\<close> by (rule inj_onI) simp
      show ?thesis
        using Cons True
        by (simp add: eq fin notin card_image inj)
    qed
  next
    case False
    with Cons show ?thesis
      by (auto simp: nth_Cons' gr0_conv_Suc intro!: bij_betw_same_card[of Suc])
  qed
qed simp

lemma count_list_lvertical: 
  \<open>count_list (lvertical lxss i) x = (if i < llength lxss then card {j. j \<le> i \<and> j < llength (lnth lxss i) \<and> lnth (lnth lxss i) j = x} else 0)\<close>
proof (cases \<open>enat i < llength lxss\<close>)
  case False
  then show ?thesis by (simp add: lvertical_def)
next
  case ili: True
  have lv: \<open>lvertical lxss i = ltaken (Suc i) (lnth lxss i)\<close>
    using ili by (simp add: lvertical_def)
  show ?thesis
  proof (cases \<open>enat (Suc i) \<le> llength (lnth lxss i)\<close>)
    case leq: True
    have len: \<open>length (ltaken (Suc i) (lnth lxss i)) = Suc i\<close>
      by (simp del: ltaken.simps add: length_ltaken leq)
    have nth: \<open>\<And>j. j < Suc i \<Longrightarrow> ltaken (Suc i) (lnth lxss i) ! j = lnth (lnth lxss i) j\<close>
      by (metis leq nth_ltaken)
    have li: \<open>\<And>j. j \<le> i \<Longrightarrow> enat j < llength (lnth lxss i)\<close>
    proof -
      fix j assume hj: \<open>j \<le> i\<close>
      have \<open>enat (Suc j) \<le> enat (Suc i)\<close> using hj by simp
      also have \<open>enat (Suc i) \<le> llength (lnth lxss i)\<close> using leq by (simp add: Suc_ile_eq)
      finally show \<open>enat j < llength (lnth lxss i)\<close> by (simp add: Suc_ile_eq)
    qed
    have set_eq: \<open>{j. j < length (ltaken (Suc i) (lnth lxss i)) \<and> ltaken (Suc i) (lnth lxss i) ! j = x}
      = {j. j \<le> i \<and> enat j < llength (lnth lxss i) \<and> lnth (lnth lxss i) j = x}\<close>
      by (auto simp del: ltaken.simps simp add: len nth li less_Suc_eq_le)
    have key: \<open>count_list (ltaken (Suc i) (lnth lxss i)) x =
        card {j. j \<le> i \<and> enat j < llength (lnth lxss i) \<and> lnth (lnth lxss i) j = x}\<close>
      by (simp only: count_list_alt set_eq)
    have \<open>count_list (lvertical lxss i) x = count_list (ltaken (Suc i) (lnth lxss i)) x\<close>
      by (simp only: lv)
    also have \<open>\<dots> = card {j. j \<le> i \<and> enat j < llength (lnth lxss i) \<and> lnth (lnth lxss i) j = x}\<close>
      by (rule key)
    also have \<open>\<dots> = (if enat i < llength lxss
        then card {j. j \<le> i \<and> enat j < llength (lnth lxss i) \<and> lnth (lnth lxss i) j = x} else 0)\<close>
      by (simp add: ili)
    finally show ?thesis .
  next
    case nleq: False
    then obtain k where fin: \<open>llength (lnth lxss i) = enat k\<close>
      by (meson less_enatE linorder_not_le)
    from nleq fin have klt: \<open>k < Suc i\<close> by (simp add: Suc_ile_eq)
    have len_eq: \<open>length (ltaken (Suc i) (lnth lxss i)) = k\<close>
      using nleq fin by (simp del: ltaken.simps add: length_ltaken)
    have nth_eq: \<open>\<And>m. m < k \<Longrightarrow> ltaken (Suc i) (lnth lxss i) ! m = lnth (lnth lxss i) m\<close>
      by (metis len_eq lnth_lappend_llist_of ltaken_ldropn_decomp)
    have li: \<open>\<And>j. j < k \<Longrightarrow> enat j < llength (lnth lxss i)\<close>
      by (simp add: fin)
    have le_i: \<open>k \<le> i\<close> using klt by simp
    have set_eq: \<open>{j. j < length (ltaken (Suc i) (lnth lxss i)) \<and> ltaken (Suc i) (lnth lxss i) ! j = x}
      = {j. j \<le> i \<and> enat j < llength (lnth lxss i) \<and> lnth (lnth lxss i) j = x}\<close>
      by (auto simp del: ltaken.simps simp add: len_eq nth_eq li fin
          dest: order_less_le_trans[OF _ le_i])
    have key: \<open>count_list (ltaken (Suc i) (lnth lxss i)) x =
        card {j. j \<le> i \<and> enat j < llength (lnth lxss i) \<and> lnth (lnth lxss i) j = x}\<close>
      by (simp only: count_list_alt set_eq)
    have \<open>count_list (lvertical lxss i) x = count_list (ltaken (Suc i) (lnth lxss i)) x\<close>
      by (simp only: lv)
    also have \<open>\<dots> = card {j. j \<le> i \<and> enat j < llength (lnth lxss i) \<and> lnth (lnth lxss i) j = x}\<close>
      by (rule key)
    also have \<open>\<dots> = (if enat i < llength lxss
        then card {j. j \<le> i \<and> enat j < llength (lnth lxss i) \<and> lnth (lnth lxss i) j = x} else 0)\<close>
      by (simp add: ili)
    finally show ?thesis .
  qed
qed

lemma llength_less_lfinite[simp]: \<open>llength lxss < enat j \<Longrightarrow> lfinite lxss\<close>
  using enat_iless lfinite_conv_llength_enat by blast

lemma ltaken_all: \<open>llength lxss < enat j \<Longrightarrow> ltaken j lxss = list_of lxss\<close>
  by (metis enat_iless length_ltaken linorder_not_le list_of_llist_of
      llength_llist_of lnth_equalityI lnth_lappend1 ltaken_ldropn_decomp
      the_enat.simps)

lemma count_list_map_filter:
  \<open>count_list (List.map_filter f xs) x = card {i. i < length xs \<and> f (xs ! i) = Some x}\<close>
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  note IH = Cons.hyps
  show ?case
  proof (cases \<open>f a\<close>)
    case None
    have set_eq: \<open>{i. i < Suc (length xs) \<and> f ((a # xs) ! i) = Some x} =
        Suc ` {i. i < length xs \<and> f (xs ! i) = Some x}\<close>
      by (auto simp: None nth_Cons' gr0_conv_Suc)
    have \<open>count_list (List.map_filter f (a # xs)) x = count_list (List.map_filter f xs) x\<close>
      by (simp add: None)
    also have \<open>\<dots> = card {i. i < length xs \<and> f (xs ! i) = Some x}\<close> by (rule IH)
    also have \<open>\<dots> = card {i. i < Suc (length xs) \<and> f ((a # xs) ! i) = Some x}\<close>
      using set_eq by (simp add: card_image)
    finally show ?thesis by simp
  next
    case (Some y)
    show ?thesis
    proof (cases \<open>y = x\<close>)
      case True
      have set_eq: \<open>{i. i < Suc (length xs) \<and> f ((a # xs) ! i) = Some x} =
          insert 0 (Suc ` {i. i < length xs \<and> f (xs ! i) = Some x})\<close>
        by (auto simp: True Some nth_Cons' less_Suc_eq_0_disj)
      have fin: \<open>finite {i. i < length xs \<and> f (xs ! i) = Some x}\<close> by simp
      have notin: \<open>0 \<notin> Suc ` {i. i < length xs \<and> f (xs ! i) = Some x}\<close> by simp
      have \<open>count_list (List.map_filter f (a # xs)) x =
          Suc (count_list (List.map_filter f xs) x)\<close>
        by (simp add: Some True)
      also have \<open>\<dots> = Suc (card {i. i < length xs \<and> f (xs ! i) = Some x})\<close> by (simp add: IH)
      also have \<open>\<dots> = card (insert 0 (Suc ` {i. i < length xs \<and> f (xs ! i) = Some x}))\<close>
        by (simp add: fin notin card_image)
      also have \<open>\<dots> = card {i. i < Suc (length xs) \<and> f ((a # xs) ! i) = Some x}\<close>
        by (simp only: set_eq)
      finally show ?thesis by simp
    next
      case False
      have set_eq: \<open>{i. i < Suc (length xs) \<and> f ((a # xs) ! i) = Some x} =
          Suc ` {i. i < length xs \<and> f (xs ! i) = Some x}\<close>
        by (auto simp: Some False nth_Cons' gr0_conv_Suc)
      have \<open>count_list (List.map_filter f (a # xs)) x = count_list (List.map_filter f xs) x\<close>
        by (simp add: Some False)
      also have \<open>\<dots> = card {i. i < length xs \<and> f (xs ! i) = Some x}\<close> by (rule IH)
      also have \<open>\<dots> = card {i. i < Suc (length xs) \<and> f ((a # xs) ! i) = Some x}\<close>
        using set_eq by (simp add: card_image)
      finally show ?thesis by simp
    qed
  qed
qed

lemma count_list_lhorizontal: 
  \<open>count_list (lhorizontal lxss j) x = card {i. i < j \<and> i < llength lxss \<and> j < llength (lnth lxss i) \<and> lnth (lnth lxss i) j = x}\<close>
  unfolding lhorizontal_def count_list_map_filter
proof (rule arg_cong[where f=card])
  show \<open>{i. i < length (ltaken j lxss) \<and> (if enat j < llength (ltaken j lxss ! i) then Some (lnth (ltaken j lxss ! i) j) else None) = Some x} =
        {i. i < j \<and> enat i < llength lxss \<and> enat j < llength (lnth lxss i) \<and> lnth (lnth lxss i) j = x}\<close>
  proof (rule set_eqI, rule iffI)
    fix i
    assume \<open>i \<in> {i. i < length (ltaken j lxss) \<and> (if enat j < llength (ltaken j lxss ! i) then Some (lnth (ltaken j lxss ! i) j) else None) = Some x}\<close>
    hence h_lt: \<open>i < length (ltaken j lxss)\<close> and h_if: \<open>enat j < llength (ltaken j lxss ! i)\<close>
      and h_x: \<open>lnth (ltaken j lxss ! i) j = x\<close>
      by (auto split: if_splits)
    have h_i_lt: \<open>enat i < llength lxss\<close>
    proof (cases \<open>enat j \<le> llength lxss\<close>)
      case True
      with h_lt have \<open>i < j\<close> by (simp add: length_ltaken)
      with True show ?thesis by (simp add: order_less_le_subst2)
    next
      case False
      with h_lt have \<open>i < the_enat (llength lxss)\<close> by (simp add: length_ltaken)
      then show ?thesis
        by (metis False enat_iless enat_ord_simps(2) linorder_not_less the_enat.simps)
    qed
    have h_key: \<open>ltaken j lxss ! i = lnth lxss i\<close>
      by (metis h_lt length_ltaken linorder_not_le llength_less_lfinite ltaken_all nth_list_of nth_ltaken)
    show \<open>i \<in> {i. i < j \<and> enat i < llength lxss \<and> enat j < llength (lnth lxss i) \<and> lnth (lnth lxss i) j = x}\<close>
      using h_lt h_if h_x h_i_lt h_key
      by (smt (verit, del_insts) order.strict_trans enat_ord_simps(2) length_ltaken
          linorder_less_linear mem_Collect_eq order.strict_iff_order)
  next
    fix i
    assume \<open>i \<in> {i. i < j \<and> enat i < llength lxss \<and> enat j < llength (lnth lxss i) \<and> lnth (lnth lxss i) j = x}\<close>
    hence h_j: \<open>i < j\<close> and h_lt: \<open>enat i < llength lxss\<close>
      and h_llength: \<open>enat j < llength (lnth lxss i)\<close> and h_x: \<open>lnth (lnth lxss i) j = x\<close>
      by auto
    have h_key: \<open>ltaken j lxss ! i = lnth lxss i\<close>
      by (metis h_j llength_less_lfinite ltaken_all not_le_imp_less nth_list_of nth_ltaken)
    show \<open>i \<in> {i. i < length (ltaken j lxss) \<and> (if enat j < llength (ltaken j lxss ! i) then Some (lnth (ltaken j lxss ! i) j) else None) = Some x}\<close>
      using h_j h_lt h_llength h_x h_key
      by (smt (verit, best) enat_ord_simps(2) length_list_of length_ltaken linorder_less_linear
          llength_less_lfinite ltaken_all mem_Collect_eq order_le_less)
  qed
qed

lemma LSUM_extend: assumes \<open>lprefix lxs lys\<close>
  \<open>\<forall>i < llength lxs. f (lnth lxs i) = g (lnth lys i)\<close>
  \<open>\<forall>i < llength lys. i \<ge> llength lxs \<longrightarrow> g (lnth lys i) = 0\<close>
  shows \<open>LSUM lxs f = LSUM lys g\<close>
proof -
  have key: \<open>LSUM lxs f = LSUM lys g\<close> if \<open>lfinite lxs\<close>
    using that assms
  proof (induct lxs arbitrary: lys rule: lfinite.induct)
    case (lfinite_LNil lys)
    have \<open>\<forall>x \<in> lset lys. g x = 0\<close>
      using lfinite_LNil(3) by (auto simp: in_lset_conv_lnth)
    then have \<open>LSUM lys g = 0\<close> by (simp add: lsum_0_iff)
    then show ?case by simp
  next
    case (lfinite_LConsI xs x lys_outer)
    obtain ys' where ys_eq: \<open>lys_outer = LCons x ys'\<close> and pre: \<open>lprefix xs ys'\<close>
      using lfinite_LConsI(3) by (auto simp: LCons_lprefix_conv)
    have eq_x: \<open>f x = g x\<close>
      using spec[OF lfinite_LConsI(4), of 0] unfolding ys_eq
      by (simp add: zero_enat_def[symmetric])
    have IH5: \<open>\<forall>i. enat i < llength xs \<longrightarrow> f (lnth xs i) = g (lnth ys' i)\<close>
    proof (intro allI impI)
      fix i assume hlt: \<open>enat i < llength xs\<close>
      then have hi: \<open>enat (Suc i) < llength (LCons x xs)\<close> by (simp add: Suc_ile_eq)
      have h5i: \<open>enat (Suc i) < llength (LCons x xs) \<longrightarrow>
          f (lnth (LCons x xs) (Suc i)) = g (lnth lys_outer (Suc i))\<close>
        by (rule spec[OF lfinite_LConsI(4), of \<open>Suc i\<close>])
      show \<open>f (lnth xs i) = g (lnth ys' i)\<close>
        using h5i hi unfolding ys_eq by simp
    qed
    have IH6: \<open>\<forall>i. enat i < llength ys' \<longrightarrow> llength xs \<le> enat i \<longrightarrow> g (lnth ys' i) = 0\<close>
    proof (intro allI impI)
      fix i assume hi: \<open>enat i < llength ys'\<close> and hi2: \<open>llength xs \<le> enat i\<close>
      have h1: \<open>enat (Suc i) < llength lys_outer\<close>
        unfolding ys_eq by (simp add: Suc_ile_eq hi)
      have h2: \<open>llength (LCons x xs) \<le> enat (Suc i)\<close>
        by (simp add: eSuc_enat[symmetric] hi2)
      have h6i: \<open>enat (Suc i) < llength lys_outer \<longrightarrow>
          llength (LCons x xs) \<le> enat (Suc i) \<longrightarrow> g (lnth lys_outer (Suc i)) = 0\<close>
        by (rule spec[OF lfinite_LConsI(5), of \<open>Suc i\<close>])
      show \<open>g (lnth ys' i) = 0\<close>
        using h6i h1 h2 unfolding ys_eq by simp
    qed
    have eq_tails: \<open>LSUM xs f = LSUM ys' g\<close>
      by (rule lfinite_LConsI(2)[of ys', OF pre IH5 IH6])
    show ?case unfolding ys_eq using eq_x eq_tails by simp
  qed
  show ?thesis
  proof (cases \<open>lfinite lxs\<close>)
    case True show ?thesis using key[OF True] .
  next
    case False then show ?thesis using assms
      by (metis in_lset_conv_lnth llist.map_cong not_lfinite_lprefix_conv_eq)
  qed
qed

lemma lupt_0[simp]: \<open>lupt i 0 = LNil\<close>
  by (cases i) auto

lemma lprefix_lupt: \<open>j \<le> k \<Longrightarrow> lprefix (lupt i j) (lupt i k)\<close>
proof (cases \<open>enat i \<le> j\<close>)
  case False
  then show ?thesis by (simp add: lnull_lprefix)
next
  case True
  assume jk: \<open>j \<le> k\<close>
  show ?thesis
  proof (cases j)
    case (enat m)
    have split: \<open>lupt i k = lappend (lupt i (enat m)) (lupt m k)\<close>
      using True[unfolded enat] jk[unfolded enat]
      by (coinduction arbitrary: i m k)
         (force simp: Suc_ile_eq not_le order_less_le_subst2 dual_order.strict_trans1 lappend_lnull1)
    then show ?thesis
      unfolding enat lprefix_conv_lappend by blast
  next
    case infinity
    then show ?thesis using True jk by simp
  qed
qed

lemma if_card_else_0: \<open>(if P z then card {x. Q x z} else 0) = card {x. P z \<and> Q x z}\<close>
  by auto

lemma LSUM_llist_of[simp]: \<open>LSUM (llist_of xs) f = sum_list (map f xs)\<close>
  by (induct xs) auto

lemma card_sum_list: \<open>(\<And>i. P i \<Longrightarrow> i \<le> n) \<Longrightarrow>
  card {i :: nat. P i} = sum_list (map (\<lambda>i. if P i then 1 else 0) [0 ..< Suc n])\<close>
proof (induct n arbitrary: P)
  case 0
  then show ?case by (auto simp: card_eq_0_iff card_1_singleton_iff)
next
  case (Suc n P)
  have bound: \<open>\<And>i. (P i \<and> i \<noteq> Suc n) \<Longrightarrow> i \<le> n\<close>
    using Suc.prems by (force simp: le_Suc_eq)
  have IH: \<open>card {i. P i \<and> i \<noteq> Suc n} =
      sum_list (map (\<lambda>i. if P i \<and> i \<noteq> Suc n then 1 else 0) [0..<Suc n])\<close>
    by (rule Suc.hyps[of \<open>\<lambda>i. P i \<and> i \<noteq> Suc n\<close>, OF bound])
  have sum_eq: \<open>sum_list (map (\<lambda>i. if P i \<and> i \<noteq> Suc n then 1 else 0) [0..<Suc n]) =
      sum_list (map (\<lambda>i. if P i then 1 else 0) [0..<Suc n])\<close>
    by (intro arg_cong[where f=sum_list] map_cong refl)
       (auto simp: le_Suc_eq dest: Suc.prems)
  show ?case
  proof (cases \<open>P (Suc n)\<close>)
    case True
    have fin: \<open>finite {i. P i \<and> i \<noteq> Suc n}\<close>
      by (rule finite_subset[of _ \<open>{0..<Suc n}\<close>])
         (auto simp: le_Suc_eq dest: Suc.prems)
    have notin: \<open>Suc n \<notin> {i. P i \<and> i \<noteq> Suc n}\<close> by simp
    have insert_eq: \<open>{i. P i} = insert (Suc n) {i. P i \<and> i \<noteq> Suc n}\<close>
      using True by auto
    have \<open>card {i. P i} = Suc (card {i. P i \<and> i \<noteq> Suc n})\<close>
      unfolding insert_eq using fin notin by simp
    also have \<open>\<dots> = Suc (sum_list (map (\<lambda>i. if P i then 1 else 0) [0..<Suc n]))\<close>
      by (metis (mono_tags, lifting) IH sum_eq)
    also have \<open>\<dots> = sum_list (map (\<lambda>i. if P i then 1 else 0) [0..<Suc (Suc n)])\<close>
      using True by simp
    finally show ?thesis .
  next
    case False
    have eq: \<open>{i. P i} = {i. P i \<and> i \<noteq> Suc n}\<close> using False by auto
    have \<open>card {i. P i} = sum_list (map (\<lambda>i. if P i then 1 else 0) [0..<Suc n])\<close>
      unfolding eq by (metis (mono_tags, lifting) IH sum_eq)
    also have \<open>\<dots> = sum_list (map (\<lambda>i. if P i then 1 else 0) [0..<Suc (Suc n)])\<close>
      using False by simp
    finally show ?thesis .
  qed
qed

lemma llist_of_lupt: \<open>llist_of [i ..< j] = lupt i j\<close>
  by (coinduction arbitrary: i j) auto

lemma enat_sum_list: \<open>enat (sum_list xs) = sum_list (map enat xs)\<close>
  by (induct xs) (auto simp: enat_0 simp flip: plus_enat_simps)

lemma card_LSUM: 
  assumes \<open>(\<And>i. P i \<Longrightarrow> i \<le> n)\<close>
  shows \<open>enat (card {i :: nat. P i}) = LSUM lenats (\<lambda>i. if P i then 1 else 0)\<close>
proof -
  have \<open>enat (card {i :: nat. P i}) =
      enat (\<Sum>i\<leftarrow>[0..<Suc n]. if P i then 1 else 0)\<close>
    using card_sum_list[OF assms] by simp
  also have \<open>\<dots> = sum_list (map (enat \<circ> (\<lambda>i. if P i then 1 else 0)) [0..<Suc n])\<close>
    by (simp only: enat_sum_list list.map_comp)
  also have \<open>\<dots> = LSUM (llist_of [0..<Suc n]) (enat \<circ> (\<lambda>i. if P i then 1 else 0))\<close>
    by (simp only: LSUM_llist_of)
  also have \<open>\<dots> = LSUM lenats (\<lambda>i. if P i then 1 else 0)\<close>
  proof (rule LSUM_extend)
    show \<open>lprefix (llist_of [0..<Suc n]) lenats\<close>
      by (simp add: llist_of_lupt lprefix_lupt del: upt.simps)
    show \<open>\<forall>i < llength (llist_of [0..<Suc n]).
        (enat \<circ> (\<lambda>i. if P i then 1 else 0)) (lnth (llist_of [0..<Suc n]) i) =
        (\<lambda>i. if P i then 1 else 0) (lnth lenats i)\<close>
      by (simp add: lnth_lupt one_enat_def enat_0 del: upt.simps)
    show \<open>\<forall>i < llength lenats.
        llength (llist_of [0..<Suc n]) \<le> enat i \<longrightarrow>
        (\<lambda>i. if P i then 1 else 0) (lnth lenats i) = 0\<close>
      by (simp add: lnth_lupt del: upt.simps) (metis assms not_less_eq_eq)
  qed
  finally show ?thesis .
qed

lemma LSUM_extend_lenats:
  \<open>LSUM lxs f =  LSUM lenats (\<lambda>i. if enat i < llength lxs then f (lnth lxs i) else 0)\<close>
proof -
  have step1: \<open>LSUM (lupt 0 (llength lxs)) (f \<circ> lnth lxs) =
    LSUM lenats (\<lambda>i. if enat i < llength lxs then f (lnth lxs i) else 0)\<close>
  proof (rule LSUM_extend)
    show \<open>lprefix (lupt 0 (llength lxs)) lenats\<close>
      by (simp add: lprefix_lupt)
  next
    show \<open>\<forall>i. enat i < llength (lupt 0 (llength lxs)) \<longrightarrow>
      (f \<circ> lnth lxs) (lnth (lupt 0 (llength lxs)) i) =
      (\<lambda>i. if enat i < llength lxs then f (lnth lxs i) else 0) (lnth lenats i)\<close>
      by (simp add: lnth_lupt)
  next
    show \<open>\<forall>i. enat i < llength lenats \<longrightarrow> llength (lupt 0 (llength lxs)) \<le> enat i \<longrightarrow>
      (\<lambda>i. if enat i < llength lxs then f (lnth lxs i) else 0) (lnth lenats i) = 0\<close>
      by (fastforce simp: lnth_lupt)
  qed
  show ?thesis
    by (subst llist_conv_lmap_lupt) (simp add: llist.map_comp flip: step1)
qed

lemma LCons_eq_lmap_conv:
  \<open>(LCons y lys = lmap f lxs) = (\<exists>x lxs'. lxs = LCons x lxs' \<and> y = f x \<and> lys = lmap f lxs')\<close>
  using lmap_eq_LCons_conv by fastforce

lemma lmap_eq_lappend: \<open>lfinite lys \<Longrightarrow> lmap f lxs = lappend lys lzs \<longleftrightarrow>
  (\<exists>lus lvs. lxs = lappend lus lvs \<and> lys = lmap f lus \<and> lzs = lmap f lvs)\<close>
proof (induct lys arbitrary: lxs rule: lfinite_induct)
  case LNil
  then show ?case
    by (auto simp: lnull_def LNil_eq_lmap)
next
  case (LCons lys lxs)
  from LCons(3)[of \<open>ltl lxs\<close>] LCons(1,2) show ?case
    by (cases lxs; cases lys)
      (fastforce simp: lnull_def lmap_eq_LCons_conv LCons_eq_lmap_conv lmap_lappend_distrib
         intro: exI[of _ \<open>LCons _ _\<close>])+
qed

lemma llist_of_eq_lmap_conv: 
  \<open>llist_of xs = lmap f lxs \<longleftrightarrow> (\<exists>ys. lxs = llist_of ys \<and> map f ys = xs)\<close>
  by (induct xs arbitrary: lxs) (force simp: LNil_eq_lmap LCons_eq_lmap_conv map_eq_Cons_conv)+

lemma neq_LCons_conv: \<open>(\<forall>x lxs. lys \<noteq> LCons x lxs) \<longleftrightarrow> lys = LNil\<close>
  by (cases lys; simp)

lemma epred_iadd: \<open>epred (a + b) = (if a = 0 then epred b else epred a + b)\<close>
  by (cases a rule: co.enat.exhaust) (auto simp: epred_iadd1)

lemma LSUM_isum: \<open>ldistinct lxs \<Longrightarrow> LSUM lxs f = isum f (lset lxs)\<close>
proof (coinduction arbitrary: lxs f)
  case eq_enat
  show ?case
  proof (intro conjI impI disjI1)
    show \<open>(LSUM lxs f = 0) = (isum f (lset lxs) = 0)\<close>
      by (auto simp: lsum_0_iff isum_eq_0_iff)
  next
    assume hne1: \<open>LSUM lxs f \<noteq> 0\<close> and hne2: \<open>isum f (lset lxs) \<noteq> 0\<close>
    have hexists: \<open>\<exists>x \<in> lset (lmap f lxs). x \<noteq> 0\<close>
      using hne1 by (auto simp: lsum_0_iff)
    have hfin: \<open>lfinite (ltakeWhile ((=) 0) (lmap f lxs))\<close>
      using hexists by (auto simp: lfinite_ltakeWhile)
    have hnotnil: \<open>ldropWhile ((=) 0) (lmap f lxs) \<noteq> LNil\<close>
      using hexists by (auto simp: ldropWhile_eq_LNil_iff)
    obtain z lzs where hlws: \<open>ldropWhile ((=) 0) (lmap f lxs) = LCons z lzs\<close>
      using hnotnil by (cases \<open>ldropWhile ((=) 0) (lmap f lxs)\<close>) auto
    have hnz: \<open>z \<noteq> 0\<close>
      using hexists hlws by (simp add: ldropWhile_eq_LCons_iff)
    define zs where \<open>zs = list_of (ltakeWhile ((=) 0) (lmap f lxs))\<close>
    have hlmap: \<open>lmap f lxs = lappend (llist_of zs) (LCons z lzs)\<close>
      unfolding zs_def using hfin hlws
      by (metis lappend_ltakeWhile_ldropWhile llist_of_list_of)
    have hzeros: \<open>\<forall>x \<in> set zs. x = 0\<close>
      using hfin lset_ltakeWhileD zs_def by fastforce
    let ?f = \<open>\<lambda>y. if y = lnth lxs (length zs) then epred (f y) else f y\<close>
    have hep1: \<open>epred (LSUM lxs f) = LSUM lxs ?f\<close>
    proof -
      { fix ys :: \<open>'a list\<close> and x :: \<open>'a\<close> and lxs' :: \<open>'a llist\<close>
        assume hall: \<open>\<forall>z\<in>set ys. f z = 0\<close> and hfx: \<open>f x \<noteq> 0\<close>
          and hnotinys: \<open>x \<notin> set ys\<close> and hnotinlxs': \<open>x \<notin> lset lxs'\<close>
        have hsum0: \<open>sum_list (map f ys) = 0\<close>
          using hall by simp
        have hsum_if0: \<open>(\<Sum>z\<leftarrow>ys. if z = x then epred (f z) else f z) = 0\<close>
          using hnotinys hall by (auto intro!: sum_list_0 split: if_splits)
        have hLSUM_eq: \<open>LSUM lxs' (\<lambda>z. if z = x then epred (f z) else f z) = LSUM lxs' f\<close>
          by (rule arg_cong[where f=\<open>lsum\<close>], rule llist.map_cong0) (use hnotinlxs' in auto)
        have \<open>epred (sum_list (map f ys) + (f x + LSUM lxs' f)) =
          (\<Sum>z\<leftarrow>ys. if z = x then epred (f z) else f z) + (epred (f x) + LSUM lxs' (\<lambda>z. if z = x then epred (f z) else f z))\<close>
          using hfx hsum0 hsum_if0 hLSUM_eq by (simp add: epred_iadd1 hsum0 hsum_if0)
      }
      thus ?thesis
        using hlmap hzeros hnz eq_enat
        by (auto simp: lmap_eq_lappend lmap_lappend_distrib lsum_lappend LCons_eq_lmap_conv
            llist_of_eq_lmap_conv ldistinct_lappend lnth_lappend2)
    qed
    have hep2: \<open>epred (isum f (lset lxs)) = isum ?f (lset lxs)\<close>
    proof -
      { fix ys :: \<open>'a list\<close> and x :: \<open>'a\<close> and lxs' :: \<open>'a llist\<close>
        assume hall: \<open>\<forall>z\<in>set ys. f z = 0\<close> and hfx: \<open>f x \<noteq> 0\<close>
          and hnotinys: \<open>x \<notin> set ys\<close> and hnotinlxs': \<open>x \<notin> lset lxs'\<close>
          and hdist: \<open>distinct ys\<close> and hsep: \<open>set ys \<inter> lset lxs' = {}\<close>
        have hisum_ys0: \<open>isum f (set ys) = 0\<close>
          using hall by (simp add: isum_eq_0_iff)
        have hisum_ys_if0: \<open>isum (\<lambda>y. if y = x then epred (f y) else f y) (set ys) = 0\<close>
          using hnotinys hall by (auto simp: isum_eq_0_iff)
        have hisum_lxs'_eq: \<open>isum (\<lambda>y. if y = x then epred (f y) else f y) (lset lxs') = isum f (lset lxs')\<close>
          using hnotinlxs' by (intro isum_cong) auto
        have \<open>epred (isum f (set ys) + isum f (lset lxs') + f x) =
          isum (\<lambda>y. if y = x then epred (f y) else f y) (set ys) +
          isum (\<lambda>y. if y = x then epred (f y) else f y) (lset lxs') + epred (f x)\<close>
          using hfx hisum_ys0 hisum_ys_if0 hisum_lxs'_eq
          by (simp add: epred_iadd hisum_ys0 hisum_ys_if0 add.commute add.assoc)
      }
      thus ?thesis
        using hlmap hzeros hnz eq_enat
        by (auto simp: lmap_eq_lappend lmap_lappend_distrib lsum_lappend LCons_eq_lmap_conv
            llist_of_eq_lmap_conv ldistinct_lappend lnth_lappend2)
    qed
    show \<open>\<exists>(lxs' :: 'a llist) f'. epred (LSUM lxs f) = LSUM lxs' f' \<and>
      epred (isum f (lset lxs)) = isum f' (lset lxs') \<and> ldistinct lxs'\<close>
      by (intro disjI1 exI[of _ lxs] exI[of _ \<open>?f\<close>]) (auto simp: hep1 hep2 eq_enat)
  qed
qed

lemma set_partition_subset: \<open>A \<subseteq> B \<Longrightarrow> B = A \<union> (B - A)\<close>
  by auto

lemma count_llist_isum: \<open>count_llist lxs x = isum (\<lambda>i. if enat i < llength lxs \<and> lnth lxs i = x then 1 else 0) UNIV\<close>
proof (coinduction arbitrary: lxs)
  case eq_enat
  show ?case
  proof -
    have h0: \<open>(count_llist lxs x = 0) = (isum (\<lambda>i. if enat i < llength lxs \<and> lnth lxs i = x then 1 else 0) UNIV = 0)\<close>
      by (auto simp: count_llist_zero_iff isum_eq_0_iff in_lset_conv_lnth)
    show ?thesis
    proof (cases \<open>count_llist lxs x = 0\<close>)
      case True
      then show ?thesis using h0 by simp
    next
      case False
      have hx_lset: \<open>x \<in> lset lxs\<close>
        using False by (simp add: count_llist_zero_iff)
      have htw_fin: \<open>lfinite (ltakeWhile ((\<noteq>) x) lxs)\<close>
        using hx_lset by (simp add: lfinite_ltakeWhile)
      obtain n where hlen_enat: \<open>llength (ltakeWhile ((\<noteq>) x) lxs) = enat n\<close>
        using lfinite_llength_enat[OF htw_fin] by blast
      have hlt_tw: \<open>llength (ltakeWhile ((\<noteq>) x) lxs) < llength lxs\<close>
        using hx_lset by (simp add: llength_ltakeWhile_lt_iff)
      have hx_at_n: \<open>lnth lxs n = x\<close>
      proof -
        have h1: \<open>\<not> ((\<noteq>) x) (lnth lxs (the_enat (llength (ltakeWhile ((\<noteq>) x) lxs))))\<close>
          by (rule lnth_llength_ltakeWhile[OF hlt_tw])
        show ?thesis using h1 hlen_enat by simp
      qed
      have hn_lt: \<open>enat n < llength lxs\<close>
        using hlt_tw hlen_enat by auto
      have hdrop_eq: \<open>ldropWhile ((\<noteq>) x) lxs = ldropn n lxs\<close>
        by (simp add: ldropWhile_eq_ldrop hlen_enat ldrop_enat)
      define lxs' where hlxs': \<open>lxs' = ltl (ldropWhile ((\<noteq>) x) lxs)\<close>
      have hlxs'_eq: \<open>lxs' = ldropn (Suc n) lxs\<close>
      proof -
        have \<open>ldropn n lxs = LCons (lnth lxs n) (ldropn (Suc n) lxs)\<close>
          using ldropn_Suc_conv_ldropn[OF hn_lt] by simp
        then show ?thesis by (simp add: hlxs' hdrop_eq)
      qed
      define f where f_def: \<open>f = (\<lambda>i. if enat i < llength lxs \<and> lnth lxs i = x then 1 else (0 :: enat))\<close>
      define g where g_def: \<open>g = (\<lambda>i. if enat i < llength lxs' \<and> lnth lxs' i = x then 1 else (0 :: enat))\<close>
      have hsel: \<open>epred (count_llist lxs x) = count_llist lxs' x\<close>
        unfolding hlxs' by (rule count_llist_sel[OF hx_lset])
      have hfbefore: \<open>\<forall>i < n. f i = 0\<close>
      proof (intro allI impI)
        fix i assume hi: \<open>i < n\<close>
        have hilt: \<open>enat i < llength (ltakeWhile ((\<noteq>) x) lxs)\<close>
          using hlen_enat hi by simp
        have hmem: \<open>lnth (ltakeWhile ((\<noteq>) x) lxs) i \<in> lset (ltakeWhile ((\<noteq>) x) lxs)\<close>
          by (rule iffD2[OF in_lset_conv_lnth]) (use hilt in auto)
        have hne: \<open>lnth (ltakeWhile ((\<noteq>) x) lxs) i \<noteq> x\<close>
          using lset_ltakeWhileD[OF hmem] by auto
        have heq2: \<open>lnth (ltakeWhile ((\<noteq>) x) lxs) i = lnth lxs i\<close>
          using ltakeWhile_nth[OF hilt] .
        show \<open>f i = 0\<close>
          unfolding f_def using hne heq2 hn_lt hlen_enat by simp
      qed
      have hfn: \<open>f n = 1\<close>
        unfolding f_def using hn_lt hx_at_n by simp
      have hfUNIV: \<open>isum f UNIV = isum f {0..<Suc n} + isum f {Suc n..}\<close>
      proof -
        have huniv: \<open>UNIV = {0..<Suc n} \<union> ({Suc n..} :: nat set)\<close> by auto
        show ?thesis by (subst huniv, rule isum_Un) auto
      qed
      have hfin_n: \<open>isum f {0..<Suc n} = 1\<close>
      proof -
        have \<open>isum f {0..<Suc n} = sum f {0..<Suc n}\<close>
          by (rule isum_eq_sum) simp
        also have \<open>\<dots> = sum f {0..<n} + f n\<close>
          by (rule sum.atLeastLessThan_Suc) simp
        also have \<open>sum f {0..<n} = 0\<close>
          by (rule sum.neutral) (use hfbefore in auto)
        finally show ?thesis using hfn by simp
      qed
      have hfg_len: \<open>enat (k + Suc n) < llength lxs \<longleftrightarrow> enat k < llength lxs'\<close> for k
        by (metis hlxs'_eq ldropn_Suc_conv_ldropn ldropn_eq_LConsD ldropn_ldropn)
      have hfg_lnth: \<open>lnth lxs (k + Suc n) = lnth lxs' k\<close> if \<open>enat k < llength lxs'\<close> for k
        unfolding hlxs'_eq using that hfg_len[of k]
        by (subst lnth_ldropn) (auto simp: add.commute)
      have hfg_eq: \<open>f (k + Suc n) = g k\<close> for k
        using hfg_lnth hfg_len by (auto simp: f_def g_def)
      have hfg: \<open>isum f {Suc n..} = isum g UNIV\<close>
      proof (rule isum_reindex_cong[where l = \<open>\<lambda>k. k + Suc n\<close>])
        show \<open>inj_on (\<lambda>k. k + Suc n) UNIV\<close> by (simp add: inj_on_def)
        show \<open>{Suc n..} = (\<lambda>k. k + Suc n) ` UNIV\<close>
          by (metis (no_types, lifting) ext add.commute add.right_neutral atLeast_0 image_add_atLeast)
        fix k show \<open>f (k + Suc n) = g k\<close> using hfg_eq by simp
      qed
      have heq: \<open>epred (isum f UNIV) = isum g UNIV\<close>
        by (simp add: hfUNIV hfin_n hfg epred_iadd1)
      then show ?thesis using h0 False hsel heq
        by (auto simp: f_def g_def intro: exI[of _ lxs'])
    qed
  qed
qed

lemma count_llist_lmerge: \<open>count_llist (lmerge lxss) x = lsum (lmap (\<lambda>lxs. count_llist lxs x) lxss)\<close>
proof -
  let ?LSUM = \<open>\<lambda>P. LSUM lenats (\<lambda>i. if P i then 1 else 0)\<close>
  let ?isum = \<open>\<lambda>P. isum (\<lambda>i. if P i then 1 else 0) UNIV\<close>
  have vert: \<open>enat (card {xa. enat z < llength lxss \<and> xa \<le> z \<and> enat xa < llength (lnth lxss z) \<and> lnth (lnth lxss z) xa = x}) =
    ?LSUM (\<lambda>i. enat z < llength lxss \<and> i \<le> z \<and> enat i < llength (lnth lxss z) \<and> lnth (lnth lxss z) i = x)\<close> for z
    by (rule card_LSUM) blast
  have horiz: \<open>enat (card {i. i < z \<and> enat i < llength lxss \<and> enat z < llength (lnth lxss i) \<and> lnth (lnth lxss i) z = x}) =
    ?LSUM (\<lambda>i. i < z \<and> enat i < llength lxss \<and> enat z < llength (lnth lxss i) \<and> lnth (lnth lxss i) z = x)\<close> for z
    by (rule card_LSUM) (rule less_imp_le, blast)
  have lset_lenats: \<open>lset lenats = (UNIV :: nat set)\<close>
    by (simp add: lset_lupt)
  have LSUM_len_isum: \<open>LSUM lenats f = isum f UNIV\<close> for f :: \<open>nat \<Rightarrow> enat\<close>
    by (simp only: LSUM_isum[OF ldistinct_lupt] lset_lenats)
  have rhs_eq: \<open>lsum (lmap (\<lambda>lxs. count_llist lxs x) lxss) =
      isum (\<lambda>a. if enat a < llength lxss then
                  isum (\<lambda>b. if enat b < llength (lnth lxss a) \<and> lnth (lnth lxss a) b = x then 1 else 0) UNIV
                else 0) UNIV\<close>
    by (subst LSUM_extend_lenats)
      (auto simp add: LSUM_len_isum count_llist_isum intro: isum_cong)
  have lhs_step1: \<open>LSUM lenats (\<lambda>i. count_list (lvertical lxss i @ lhorizontal lxss i) x) =
      LSUM lenats (\<lambda>z.
        ?LSUM (\<lambda>i. enat z < llength lxss \<and> i \<le> z \<and> enat i < llength (lnth lxss z) \<and> lnth (lnth lxss z) i = x) +
        ?LSUM (\<lambda>i. i < z \<and> enat i < llength lxss \<and> enat z < llength (lnth lxss i) \<and> lnth (lnth lxss i) z = x))\<close>
    unfolding plus_enat_simps(1)[symmetric] lsum_lmap_add count_list_append
      count_list_lvertical count_list_lhorizontal
    by (subst if_card_else_0) (auto simp: vert horiz)
  also have lhs_step2: \<open>\<dots> =
      isum (\<lambda>z.
        ?isum (\<lambda>i. enat z < llength lxss \<and> i \<le> z \<and> enat i < llength (lnth lxss z) \<and> lnth (lnth lxss z) i = x) +
        ?isum (\<lambda>i. i < z \<and> enat i < llength lxss \<and> enat z < llength (lnth lxss i) \<and> lnth (lnth lxss i) z = x)) UNIV\<close>
    by (simp only: LSUM_len_isum)
  also have lhs_step3: \<open>\<dots> =
      isum (\<lambda>z. ?isum (\<lambda>i. enat z < llength lxss \<and> i \<le> z \<and> enat i < llength (lnth lxss z) \<and> lnth (lnth lxss z) i = x)) UNIV +
      isum (\<lambda>z. ?isum (\<lambda>i. i < z \<and> enat i < llength lxss \<and> enat z < llength (lnth lxss i) \<and> lnth (lnth lxss i) z = x)) UNIV\<close>
    by (rule isum_plus)
  also have lhs_step4: \<open>isum (\<lambda>z. ?isum (\<lambda>i. i < z \<and> enat i < llength lxss \<and> enat z < llength (lnth lxss i) \<and> lnth (lnth lxss i) z = x)) UNIV =
      isum (\<lambda>a. ?isum (\<lambda>z. a < z \<and> enat a < llength lxss \<and> enat z < llength (lnth lxss a) \<and> lnth (lnth lxss a) z = x)) UNIV\<close>
    by (rule isum_swap)
  finally have lhs_eq: \<open>LSUM lenats (\<lambda>i. count_list (lvertical lxss i @ lhorizontal lxss i) x) =
      isum (\<lambda>a. if enat a < llength lxss then
                  isum (\<lambda>b. if enat b < llength (lnth lxss a) \<and> lnth (lnth lxss a) b = x then 1 else 0) UNIV
                else 0) UNIV\<close>
    by (unfold isum_plus[symmetric]) (auto intro!: isum_cong)
  show ?thesis
    unfolding lmerge_def count_llist_lflat
    using lhs_eq rhs_eq by (auto simp: llist.map_comp)
qed

section \<open>Countable Multisets as a Subtype\<close>

lift_definition cmcount :: \<open>'a cmset \<Rightarrow> 'a \<Rightarrow> enat\<close> is count_llist
  by (auto simp: eq_cmset_def)

lift_definition cmempty :: \<open>'a cmset\<close> is LNil .

lemma cmcount_cmempty[simp]: \<open>cmcount cmempty x = 0\<close>
  by transfer auto

lemma countable_nonzero_cmcount:
  fixes M :: \<open>'a cmset\<close>
  shows \<open>countable {x. cmcount M x \<noteq> 0}\<close>
proof (transfer)
  fix lxs :: \<open>'a llist\<close>
  show \<open>countable {x. count_llist lxs x \<noteq> 0}\<close>
  proof (rule countable_subset[of _ \<open>lset lxs\<close>])
    show \<open>{x. count_llist lxs x \<noteq> 0} \<subseteq> lset lxs\<close>
      by (auto simp: count_llist_zero_iff)
    have \<open>countable {i. enat i < llength lxs}\<close>
      by simp
    from countable_image[OF this, where f=\<open>lnth lxs\<close>] show \<open>countable (lset lxs)\<close>
      by (elim countable_subset[rotated]) (auto simp: lset_conv_lnth)
  qed
qed

lemma countable_exists_llist:
  assumes \<open>countable X\<close>
  shows \<open>\<exists>lxs. lset lxs = X \<and> ldistinct lxs\<close>
proof (cases \<open>finite X\<close>)
  case True
  then show ?thesis
  proof (induct X)
    case empty
    then show ?case
      by (auto intro: exI[of _ LNil])
  next
    case (insert x F)
    then show ?case
      by (auto intro: exI[of _ \<open>LCons x _\<close>])
  qed
next
  case False
  with assms obtain g where g: \<open>bij_betw (g :: nat \<Rightarrow> 'a) UNIV X\<close>
    using bij_betw_from_nat_into by blast
  then show ?thesis
    by (intro exI[of _ \<open>lmap g lenats\<close>])
      (auto simp: bij_betw_def image_iff inj_on_def lset_lupt)
qed

lemma in_range_cmcount:
  assumes \<open>countable {x :: 'a. f x \<noteq> 0}\<close>
  shows \<open>f \<in> range cmcount\<close>
proof -
  from assms obtain lxs where lxs: \<open>ldistinct lxs\<close> \<open>lset lxs = {x :: 'a. f x \<noteq> 0}\<close>
    using countable_exists_llist by blast
  define lys where \<open>lys = lmerge (lmap (\<lambda>x. lmap (\<lambda>_. x) (lupt 0 (f x))) lxs)\<close>
  have \<open>count_llist lys x = f x\<close> for x
    unfolding lys_def count_llist_lmerge
    by (cases \<open>f x = 0\<close>) (auto simp: llist.map_comp LSUM_isum lxs count_llist_lmap_const isum_eq_0_iff
       intro: isum_eq_singl cong: if_cong)
  then show ?thesis
    by (intro image_eqI[of _ _ \<open>abs_cmset lys\<close>]) (auto simp: cmcount.abs_eq)
qed

lemma inj_cmcount: \<open>inj cmcount\<close>
  unfolding inj_on_def
  by transfer (auto simp: eq_cmset_def)

lemma type_definition_cmset: \<open>type_definition cmcount (inv cmcount) {f. countable {x. f x \<noteq> 0}}\<close>
  by standard (auto simp: inj_cmcount in_range_cmcount inv_f_f f_inv_into_f countable_nonzero_cmcount)

corec (friend) linterleave where
  \<open>linterleave lxs lys = (case (lxs, lys) of
     (LCons x lxs', LCons y lys') \<Rightarrow> LCons x (LCons y (linterleave lxs' lys'))
   | (LCons x lxs', LNil) \<Rightarrow> LCons x lxs'
   | (LNil, LCons y lys') \<Rightarrow> LCons y lys'
   | (LNil, LNil) \<Rightarrow> LNil)\<close>
simps_of_case linterleave_simps[simp]: linterleave.code[unfolded prod.case]

lemma linterleave_LNil[simp]:
  \<open>linterleave LNil lys = lys\<close>
  \<open>linterleave lys LNil = lys\<close>
  by (cases lys; simp)+ 

lemma linterleave_LCons1[simp]:
  \<open>linterleave (LCons x lxs) lys = LCons x (linterleave lys lxs)\<close>
proof (coinduction arbitrary: x lxs lys rule: llist.coinduct_upto)
  case Eq_llist
  then show ?case
    by (subst (9 10) linterleave.code)
      (auto 5 0 split: llist.splits intro: llist.cong_intros)
qed

lemma lset_linterleave1:
  \<open>x \<in> lset (linterleave lxs lys) \<Longrightarrow>
   x \<in> lset lxs \<union> lset lys\<close>
proof (induct \<open>linterleave lxs lys\<close> arbitrary: lxs lys rule: lset_induct)
  case (find lxs' lxs)
  then show ?case
    by (cases lxs) auto
next
  case (step x' lxs' lxs)
  then show ?case
    by (cases lxs) auto
qed

lemma lset_linterleave2:
  \<open>x \<in> lset lxs \<Longrightarrow> x \<in> lset (linterleave lxs lys)\<close>
proof (induct lxs arbitrary: lys rule: lset_induct)
  case (find lxs)
  then show ?case
    by auto
next
  case (step x' lxs')
  then show ?case
    by (cases lys) (auto split: llist.splits)
qed

lemma lset_linterleave3:
  \<open>x \<in> lset lys \<Longrightarrow>
   x \<in> lset (linterleave lxs lys)\<close>
proof (induct lys arbitrary: lxs rule: lset_induct)
  case (find lys)
  then show ?case
    by (cases lxs) auto
next
  case (step x' lxs')
  then show ?case
    by (cases lxs) (auto split: llist.splits)
qed

lemma lset_linterleave[simp]:
  \<open>lset (linterleave lxs lys) = lset lxs \<union> lset lys\<close>
  by (auto dest: lset_linterleave1 lset_linterleave2 lset_linterleave3)

lemma ldistinct_linterleave: \<open>ldistinct lxs \<Longrightarrow> ldistinct lys \<Longrightarrow> lset lxs \<inter> lset lys = {} \<Longrightarrow> ldistinct (linterleave lxs lys)\<close>
proof (coinduction arbitrary: lxs lys)
  case (ldistinct lxs lys)
  then show ?case
    by (cases lxs; cases lys; force intro!: linterleave_LCons1[symmetric])
qed

coinductive linfinite where
  \<open>linfinite lxs \<Longrightarrow> linfinite (LCons x lxs)\<close>

inductive linfinite_cong for R where
  \<open>R lxs \<Longrightarrow> linfinite_cong R lxs\<close>
| \<open>linfinite lxs \<Longrightarrow> linfinite_cong R lxs\<close>
| \<open>linfinite_cong R lxs \<Longrightarrow> linfinite_cong R (LCons x lxs)\<close>

lemma linfinite_coinduct_upto[consumes 1, case_names linfinite]:
  assumes \<open>X lxs\<close> \<open>\<And>lys. X lys \<Longrightarrow> \<exists>lxs x. lys = LCons x lxs \<and> linfinite_cong X lxs\<close>
  shows \<open>linfinite lxs\<close>
proof (rule linfinite.coinduct[of \<open>linfinite_cong X\<close>])
  show \<open>linfinite_cong X lxs\<close> by (rule linfinite_cong.intros(1)) (rule assms(1))
next
  fix lxs
  assume \<open>linfinite_cong X lxs\<close>
  then show \<open>\<exists>lxs' x. lxs = LCons x lxs' \<and> (linfinite_cong X lxs' \<or> linfinite lxs')\<close>
  proof (induct lxs rule: linfinite_cong.induct)
    case (1 lxs)
    from assms(2)[OF 1] show ?case by (auto intro: linfinite_cong.intros(3))
  next
    case (2 lxs)
    then show ?case by (auto elim: linfinite.cases intro: linfinite_cong.intros(2))
  next
    case (3 lxs y)
    then show ?case by (auto intro: linfinite_cong.intros)
  qed
qed


inductive_cases linfinite_LNilE[elim!]: \<open>linfinite LNil\<close>
inductive_cases linfinite_LConsE[elim!]: \<open>linfinite (LCons x lxs)\<close>

lemma linfinite_linterleaveL: \<open>linfinite lxs \<Longrightarrow> linfinite (linterleave lxs lys)\<close>
proof (coinduction arbitrary: lxs lys rule: linfinite_coinduct_upto)
  case (linfinite lxs lys)
  then show ?case by (cases lxs; cases lys; auto intro: linfinite_cong.intros)
qed

lemma linfinite_linterleaveR: \<open>linfinite lys \<Longrightarrow> linfinite (linterleave lxs lys)\<close>
proof (coinduction arbitrary: lxs lys rule: linfinite_coinduct_upto)
  case (linfinite lxs lys)
  then show ?case by (cases lxs; cases lys; auto intro: linfinite_cong.intros)
qed

lemma lfinite_imp_not_linfinite: \<open>lfinite lxs \<Longrightarrow> \<not> linfinite lxs\<close>
  by (induct lxs rule: lfinite_induct) (auto simp: lnull_def neq_LNil_conv)

lemma not_lfinite_imp_linfinite: \<open>\<not> lfinite lxs \<Longrightarrow> linfinite lxs\<close>
proof (coinduction arbitrary: lxs)
  case (linfinite lxs)
  then show ?case by (cases lxs) auto
qed

lemma linfinite_eq_not_lfinite: \<open>linfinite lxs \<longleftrightarrow> \<not> lfinite lxs\<close>
  using lfinite_imp_not_linfinite not_lfinite_imp_linfinite by blast
lemma linfinite_eq_llength: \<open>linfinite lxs \<longleftrightarrow> llength lxs = \<infinity>\<close>
  using lfinite_imp_not_linfinite llength_eq_infty_conv_lfinite not_lfinite_imp_linfinite by blast

lemma llength_linterleave[simp]: \<open>llength (linterleave lxs lys) = llength lxs + llength lys\<close>
proof (cases \<open>linfinite lxs\<close>)
  case True
  then show ?thesis
  proof (cases \<open>linfinite lys\<close>)
    case True
    then show ?thesis
      by (metis \<open>linfinite lxs\<close> linfinite_eq_llength linfinite_linterleaveL plus_enat_simps(3))
  next
    case False
    then show ?thesis
      by (metis \<open>linfinite lxs\<close> linfinite_eq_llength linfinite_linterleaveL plus_enat_simps(2))
  qed
next
  case False
  then have hlxs: \<open>lfinite lxs\<close> by (simp add: linfinite_eq_not_lfinite)
  show ?thesis
  proof (cases \<open>linfinite lys\<close>)
    case True
    then show ?thesis by (metis linfinite_eq_llength linfinite_linterleaveR plus_enat_simps(3))
  next
    case False
    then have hlys: \<open>lfinite lys\<close> by (simp add: linfinite_eq_not_lfinite)
    from hlxs hlys show ?thesis
    proof (induct lxs arbitrary: lys rule: lfinite_induct)
      case (LNil xs)
      then show ?case by (auto simp: lnull_def neq_LNil_conv)
    next
      case (LCons lxs)
      note outer_IH = \<open>\<And>lys. lfinite lys \<Longrightarrow> llength (linterleave (ltl lxs) lys) = llength (ltl lxs) + llength lys\<close>
      from \<open>lfinite lys\<close> show ?case
      proof (induct lys rule: lfinite_induct)
        case LNil
        with \<open>\<not> lnull lxs\<close> show ?case by (auto simp: lnull_def neq_LNil_conv add.commute iadd_Suc_right)
      next
        case (LCons lys)
        show ?case
        proof -
          from \<open>\<not> lnull lxs\<close> obtain x xs' where lxs_eq: \<open>lxs = LCons x xs'\<close>
            by (cases lxs) (auto simp: lnull_def)
          from \<open>\<not> lnull lys\<close> obtain y lys' where lys_eq: \<open>lys = LCons y lys'\<close>
            by (cases lys) (auto simp: lnull_def)
          from \<open>lfinite lys\<close> have fin_lys': \<open>lfinite lys'\<close>
            by (simp add: lys_eq)
          from fin_lys' have ih_lys': \<open>llength (linterleave xs' lys') = llength xs' + llength lys'\<close>
            using outer_IH[of lys'] lxs_eq by simp
          show ?case
            by (simp only: lxs_eq lys_eq linterleave_simps llength_LCons ih_lys' iadd_Suc_right add.commute)
        qed
      qed
    qed
  qed
qed

lemma lnth_linterleave_swap: 
  \<open>lnth (linterleave lxs lys) i \<notin> lset lys \<Longrightarrow> i < llength (linterleave lxs lys) \<Longrightarrow>
   \<exists>j < min (Suc i) (llength lxs). lnth (linterleave lxs lys) i = lnth lxs j\<close>
proof (induct i arbitrary: lxs lys rule: less_induct)
  case (less i lxs lys)
  show ?case
  proof (cases i)
    case 0
    with less.prems show ?thesis
      by (cases lxs; cases lys) (auto simp: enat_0)
  next
    case (Suc j)
    with less.prems less.hyps show ?thesis
    proof (cases lxs)
      case LNil
      then show ?thesis
      proof (cases lys)
        case LNil
        with less.prems \<open>lxs = LNil\<close> show ?thesis by (auto simp: Suc_ile_eq)
      next
        case (LCons b lys')
        with less.prems \<open>lxs = LNil\<close> \<open>i = Suc j\<close> show ?thesis
          by (auto simp: in_lset_conv_lnth lnth_LCons' Suc_ile_eq)
      qed
    next
      case (LCons a lxs')
      show ?thesis
      proof (cases lys)
        case LNil
        with less.prems less.hyps \<open>lxs = LCons a lxs'\<close> show ?thesis
          by (auto simp: Suc_ile_eq in_lset_conv_lnth lnth_LCons' gr0_conv_Suc less_Suc_eq_le)
      next
        case (LCons b lys')
        note lxs_eq = \<open>lxs = LCons a lxs'\<close> and lys_eq = \<open>lys = LCons b lys'\<close>
        show ?thesis
        proof (cases j)
          case 0
          with less.prems lxs_eq lys_eq \<open>i = Suc j\<close> show ?thesis
            by (auto simp: Suc_ile_eq in_lset_conv_lnth lnth_LCons')
        next
          case (Suc m)
          with less.prems less.hyps lxs_eq lys_eq \<open>i = Suc j\<close> have
            IH: \<open>lnth (linterleave lxs' lys') m \<notin> lset lys' \<Longrightarrow>
                 enat m < llength (linterleave lxs' lys') \<Longrightarrow>
                 \<exists>j'. enat j' < min (enat (Suc m)) (llength lxs') \<and>
                      lnth (linterleave lxs' lys') m = lnth lxs' j'\<close>
            by (auto simp: Suc_ile_eq less_Suc_eq_le)
          from less.prems lxs_eq lys_eq \<open>i = Suc j\<close> \<open>j = Suc m\<close>
          have notin: \<open>lnth (linterleave lxs' lys') m \<notin> lset lys'\<close>
            by (auto simp: Suc_ile_eq in_lset_conv_lnth lnth_LCons')
          from less.prems lxs_eq lys_eq \<open>i = Suc j\<close> \<open>j = Suc m\<close>
          have len: \<open>enat m < llength (linterleave lxs' lys')\<close>
            by (auto simp: Suc_ile_eq)
          from IH[OF notin len] obtain j' where
            j'_bound: \<open>enat j' < min (enat (Suc m)) (llength lxs')\<close>
            and j'_eq: \<open>lnth (linterleave lxs' lys') m = lnth lxs' j'\<close>
            by blast
          from j'_bound j'_eq \<open>i = Suc j\<close> \<open>j = Suc m\<close> lxs_eq lys_eq less.prems
          show ?thesis
            by (auto simp: Suc_ile_eq in_lset_conv_lnth lnth_LCons' intro!: exI[of _ \<open>Suc j'\<close>])
        qed
      qed
    qed
  qed
qed

lemma ldropWhile_eq_ldropn:
  \<open>\<exists>x \<in> lset lxs. \<not> P x \<Longrightarrow> \<exists>n. enat n = llength (ltakeWhile P lxs) \<and> ldropWhile P lxs = ldropn n lxs\<close>
  by (metis ldropWhile_eq_ldrop ldrop_enat lfinite_llength_enat lfinite_ltakeWhile)

lemma ltl_linterleave[simp]: \<open>\<not>lnull lxs \<Longrightarrow> ltl (linterleave lxs lys) = linterleave lys (ltl lxs)\<close>
  by (cases lxs) auto

lemma linfinite_ltl[simp]: \<open>linfinite lxs \<Longrightarrow> linfinite (ltl lxs)\<close>
  by (cases lxs) auto

lemma linfinite_ldropn[simp]: \<open>linfinite lxs \<Longrightarrow> linfinite (ldropn n lxs)\<close>
  by (induct n arbitrary: lxs) (auto simp: ldropn_Suc split: llist.splits)

lemma linfinite_not_lnull: \<open>linfinite lxs \<Longrightarrow> \<not> lnull lxs\<close>
  by (cases lxs) auto

lemma ldropn_linterleave: \<open>linfinite lxs \<Longrightarrow> linfinite lys \<Longrightarrow> ldropn n (linterleave lxs lys) = 
  (if \<exists>m. n = 2 * m then linterleave (ldropn (n div 2) lxs) (ldropn (n div 2) lys) else
  linterleave (ldropn (n div 2) lys) (ldropn (Suc (n div 2)) lxs))\<close>
proof (induct n arbitrary: lxs lys)
  case 0
  then show ?case by simp
next
  case (Suc n lxs lys)
  from Suc.prems(1) obtain a lxs' where lxs_eq: \<open>lxs = LCons a lxs'\<close> and linf_lxs': \<open>linfinite lxs'\<close>
    by (cases lxs) (auto dest: linfinite_not_lnull)
  have step: \<open>ldropn (Suc n) (linterleave lxs lys) = ldropn n (linterleave lys lxs')\<close>
    unfolding lxs_eq by (simp add: ldropn_Suc)
  have IH: \<open>ldropn n (linterleave lys lxs') =
    (if \<exists>m. n = 2 * m then linterleave (ldropn (n div 2) lys) (ldropn (n div 2) lxs')
     else linterleave (ldropn (n div 2) lxs') (ldropn (Suc (n div 2)) lys))\<close>
    by (rule Suc.hyps[OF Suc.prems(2) linf_lxs'])
  show ?case
    unfolding step lxs_eq linterleave_LCons1 ldropn_Suc_LCons IH
    by (metis even_Suc even_Suc_div_two even_mult_iff even_two_times_div_two ldropn_Suc_LCons odd_Suc_div_two)
qed

lemma llength_ltakeWhile_linterleave_ge:
  \<open>enat (2 * m) \<le> llength (ltakeWhile ((\<noteq>) x) (linterleave lxs lys)) \<Longrightarrow>
  x \<notin> set (ltaken m lxs) \<and> x \<notin> set (ltaken m lys)\<close>
proof (induct m arbitrary: lxs lys)
  case 0
  then show ?case by simp
next
  case (Suc m lxs lys)
  show ?case
  proof (cases lxs)
    case LNil
    then have hlen_lys: \<open>enat (2 * Suc m) \<le> llength (ltakeWhile ((\<noteq>) x) lys)\<close>
      using Suc.prems by simp
    have xnot: \<open>x \<notin> lset (ltakeWhile ((\<noteq>) x) lys)\<close> by (metis (full_types) lset_ltakeWhileD)
    with hlen_lys llength_ltakeWhile_le[of \<open>(\<noteq>) x\<close> lys] have \<open>x \<notin> set (ltaken (Suc m) lys)\<close>
    proof -
      have hlys_len: \<open>enat (Suc m) \<le> llength lys\<close>
        by (rule order_trans[OF _ llength_ltakeWhile_le[of \<open>(\<noteq>) x\<close> lys]])
           (rule order_trans[OF _ hlen_lys], simp)
      have neq: \<open>\<And>i. i < Suc m \<Longrightarrow> lnth lys i \<noteq> x\<close>
      proof (intro notI)
        fix i assume h_i: \<open>i < Suc m\<close> \<open>lnth lys i = x\<close>
        have \<open>enat i < enat (2 * Suc m)\<close> using h_i(1) by simp
        hence hi_lt: \<open>enat i < llength (ltakeWhile ((\<noteq>) x) lys)\<close>
          using hlen_lys by (rule order_less_le_trans)
        hence \<open>lnth lys i \<in> lset (ltakeWhile ((\<noteq>) x) lys)\<close>
          by (auto simp: in_lset_conv_lnth ltakeWhile_nth)
        then have \<open>lnth lys i \<noteq> x\<close> using lset_ltakeWhileD by fastforce
        with h_i(2) show False by simp
      qed
      show ?thesis
        unfolding set_ltaken_conv[OF hlys_len]
        by (clarsimp; use neq in fastforce)
    qed
    then show ?thesis using LNil by simp
  next
    case (LCons a lxs') note lxs_eq = this
    show ?thesis
    proof (cases lys)
      case LNil
      then have hlen_lxs: \<open>enat (2 * Suc m) \<le> llength (ltakeWhile ((\<noteq>) x) lxs)\<close>
        using Suc.prems lxs_eq by simp
      have xnot: \<open>x \<notin> lset (ltakeWhile ((\<noteq>) x) lxs)\<close> by (metis (full_types) lset_ltakeWhileD)
      with hlen_lxs llength_ltakeWhile_le[of \<open>(\<noteq>) x\<close> lxs] have \<open>x \<notin> set (ltaken (Suc m) lxs)\<close>
      proof -
        have hlxs_len: \<open>enat (Suc m) \<le> llength lxs\<close>
          by (rule order_trans[OF _ llength_ltakeWhile_le[of \<open>(\<noteq>) x\<close> lxs]])
             (rule order_trans[OF _ hlen_lxs], simp)
        have neq: \<open>\<And>i. i < Suc m \<Longrightarrow> lnth lxs i \<noteq> x\<close>
        proof (intro notI)
          fix i assume h_i: \<open>i < Suc m\<close> \<open>lnth lxs i = x\<close>
          have \<open>enat i < enat (2 * Suc m)\<close> using h_i(1) by simp
          hence hi_lt: \<open>enat i < llength (ltakeWhile ((\<noteq>) x) lxs)\<close>
            using hlen_lxs by (rule order_less_le_trans)
          hence \<open>lnth lxs i \<in> lset (ltakeWhile ((\<noteq>) x) lxs)\<close>
            by (auto simp: in_lset_conv_lnth ltakeWhile_nth)
          then have \<open>lnth lxs i \<noteq> x\<close> using lset_ltakeWhileD by fastforce
          with h_i(2) show False by simp
        qed
        show ?thesis
          unfolding set_ltaken_conv[OF hlxs_len]
          by (clarsimp; use neq in fastforce)
      qed
      then show ?thesis using LNil lxs_eq by simp
    next
      case (LCons b lys') note lys_eq = this
      have hlen: \<open>enat (2 * Suc m) \<le> llength (ltakeWhile ((\<noteq>) x)
            (LCons a (LCons b (linterleave lxs' lys'))))\<close>
        using Suc.prems unfolding lxs_eq lys_eq by simp
      have ha: \<open>a \<noteq> x\<close>
        using hlen by (auto simp: Suc_ile_eq enat_0_iff split: if_splits)
      have hlen': \<open>enat (2 * Suc m - 1) \<le> llength (ltakeWhile ((\<noteq>) x)
            (LCons b (linterleave lxs' lys')))\<close>
        using hlen ha by (simp add: Suc_ile_eq)
      have hb: \<open>b \<noteq> x\<close>
        using hlen' by (auto simp: Suc_ile_eq enat_0_iff split: if_splits)
      have hlen'': \<open>enat (2 * m) \<le> llength (ltakeWhile ((\<noteq>) x) (linterleave lxs' lys'))\<close>
        using hlen' hb by (simp add: Suc_ile_eq)
      note IH = Suc.hyps[OF hlen'']
      show ?thesis using ha hb IH unfolding lxs_eq lys_eq by simp
    qed
  qed
qed

lemma llength_ltakeWhile_linterleave_eq:
  \<open>enat (2 * m) = llength (ltakeWhile ((\<noteq>) x) (linterleave lxs lys)) \<Longrightarrow>
  x \<notin> set (ltaken m lxs) \<and> x \<notin> set (ltaken m lys)\<close>
  by (rule llength_ltakeWhile_linterleave_ge) auto

lemma llength_ltakeWhile_linterleave_ge_Suc:
  \<open>linfinite lxs \<Longrightarrow> linfinite lys \<Longrightarrow>
   enat (Suc (2 * m)) \<le> llength (ltakeWhile ((\<noteq>) x) (linterleave lxs lys)) \<Longrightarrow>
  x \<notin> set (ltaken (Suc m) lxs) \<and> x \<notin> set (ltaken m lys)\<close>
proof (induct m arbitrary: lxs lys)
  case 0
  then show ?case by (auto simp: enat_0_iff Suc_ile_eq split: if_splits)
next
  case (Suc m lxs lys)
  from Suc.prems(1) obtain a lxs' where lxs_eq: \<open>lxs = LCons a lxs'\<close>
    by (cases lxs) (auto dest: linfinite_not_lnull)
  from Suc.prems(2) obtain b lys' where lys_eq: \<open>lys = LCons b lys'\<close>
    by (cases lys) (auto dest: linfinite_not_lnull)
  from Suc.prems lxs_eq lys_eq have linf_tails: \<open>linfinite lxs'\<close> \<open>linfinite lys'\<close>
    by auto
  from Suc.prems lxs_eq lys_eq have prems': \<open>x \<noteq> a\<close> \<open>x \<noteq> b\<close>
    \<open>enat (Suc (2 * m)) \<le> llength (ltakeWhile ((\<noteq>) x) (linterleave lxs' lys'))\<close>
    by (auto simp: Suc_ile_eq split: if_splits)
  from Suc.hyps[OF linf_tails(1) linf_tails(2) prems'(3)]
  have IH: \<open>x \<notin> set (ltaken (Suc m) lxs') \<and> x \<notin> set (ltaken m lys')\<close> .
  from IH prems' lxs_eq lys_eq show ?case
    by (auto simp: Suc_ile_eq split: if_splits)
qed

lemma llength_ltakeWhile_linterleave_eq_Suc:
  \<open>linfinite lxs \<Longrightarrow> linfinite lys \<Longrightarrow>
   enat (Suc (2 * m)) = llength (ltakeWhile ((\<noteq>) x) (linterleave lxs lys)) \<Longrightarrow>
  x \<notin> set (ltaken (Suc m) lxs) \<and> x \<notin> set (ltaken m lys)\<close>
  by (rule llength_ltakeWhile_linterleave_ge_Suc) auto

lemma count_llist_linterleave: 
  \<open>count_llist (linterleave lxs lys) x = count_llist lxs x + count_llist lys x\<close>
proof ((cases \<open>lfinite lxs\<close>; cases \<open>lfinite lys\<close>), goal_cases FF FI IF II)
  case FF
  then show ?case
  proof (induct lxs arbitrary: lys)
    case (lfinite_LConsI lxs x)
    then show ?case
      by (cases lys) (auto simp: iadd_Suc_right ac_simps)
  qed simp
next
  case FI
  then show ?case
  proof (induct lxs arbitrary: lys)
    case (lfinite_LConsI lxs x)
    then show ?case
      by (cases lys) (auto simp: iadd_Suc_right ac_simps)
  qed simp
next
  case IF
  from IF(2,1) show ?case
  proof (induct lys arbitrary: lxs)
    case (lfinite_LConsI lxs x)
    then show ?case
      by (cases lxs) (auto simp: iadd_Suc_right ac_simps)
  qed simp
next
  case II
  then show ?case
  proof (coinduction arbitrary: lxs lys)
    case eq_enat
    show ?case
    proof (cases \<open>x \<in> lset (linterleave lxs lys)\<close>)
      case False
      then show ?thesis
        using eq_enat by (auto simp: count_llist_zero_iff linfinite_eq_not_lfinite)
    next
      case True
      then have hin: \<open>x \<in> lset (linterleave lxs lys)\<close> .
      obtain n where
        h_len: \<open>enat n = llength (ltakeWhile ((\<noteq>) x) (linterleave lxs lys))\<close> and
        h_drop: \<open>ldropWhile ((\<noteq>) x) (linterleave lxs lys) = ldropn n (linterleave lxs lys)\<close>
        using ldropWhile_eq_ldropn[of \<open>linterleave lxs lys\<close> \<open>(\<noteq>) x\<close>] hin by auto
      have h_lhd: \<open>lhd (ldropWhile ((\<noteq>) x) (linterleave lxs lys)) = x\<close>
      proof -
        have hlt: \<open>llength (ltakeWhile ((\<noteq>) x) (linterleave lxs lys)) < llength (linterleave lxs lys)\<close>
          by (subst llength_ltakeWhile_lt_iff) (use hin in auto)
        have h1: \<open>lhd (ldropWhile ((\<noteq>) x) (linterleave lxs lys)) =
            lnth (linterleave lxs lys) (the_enat (llength (ltakeWhile ((\<noteq>) x) (linterleave lxs lys))))\<close>
          by (rule lhd_ldropWhile_conv_lnth) (use hin in auto)
        have h2: \<open>\<not> ((\<noteq>) x) (lnth (linterleave lxs lys)
            (the_enat (llength (ltakeWhile ((\<noteq>) x) (linterleave lxs lys)))))\<close>
          by (rule lnth_llength_ltakeWhile[OF hlt])
        from h1 h2 show ?thesis by simp
      qed

      show ?thesis
      proof (cases \<open>\<exists>m. n = 2 * m\<close>)
        case True
        then obtain m :: nat where hm: \<open>n = 2 * m\<close> by auto
        have h_drop2: \<open>ldropWhile ((\<noteq>) x) (linterleave lxs lys) =
            linterleave (ldropn m lxs) (ldropn m lys)\<close>
          using h_drop hm eq_enat
          by (simp add: ldropn_linterleave linfinite_eq_not_lfinite)
        have h_hd_lxs: \<open>lhd (ldropn m lxs) = x\<close>
        proof -
          have hnn: \<open>\<not> lnull (ldropn m lxs)\<close>
            by (metis eq_enat(1) linfinite_ldropn linfinite_not_lnull linfinite_eq_not_lfinite)
          have \<open>lhd (linterleave (ldropn m lxs) (ldropn m lys)) = lhd (ldropn m lxs)\<close>
            by (cases \<open>ldropn m lxs\<close>) (use hnn in auto)
          with h_lhd h_drop2 show ?thesis by simp
        qed
        have h_taken: \<open>x \<notin> set (ltaken m lxs) \<and> x \<notin> set (ltaken m lys)\<close>
          by (rule llength_ltakeWhile_linterleave_eq[of m]) (simp add: h_len[symmetric] hm)
        have h_lxs_eq: \<open>ldropn m lxs = LCons x (ltl (ldropn m lxs))\<close>
        proof -
          have hnn: \<open>\<not> lnull (ldropn m lxs)\<close>
            by (metis eq_enat(1) linfinite_ldropn linfinite_not_lnull linfinite_eq_not_lfinite)
          from lhd_LCons_ltl[OF hnn] h_hd_lxs show ?thesis by simp
        qed
        have h_lxs_cnt: \<open>count_llist lxs x = eSuc (count_llist (ltl (ldropn m lxs)) x)\<close>
        proof -
          have heq_lxs: \<open>lxs = lappend (llist_of (ltaken m lxs)) (ldropn m lxs)\<close>
            by (rule ltaken_ldropn_decomp)
          have hcnt_lxs: \<open>count_llist lxs x = count_llist (ldropn m lxs) x\<close>
            by (subst heq_lxs, simp only: count_llist_lappend lfinite_llist_of if_True,
                simp add: h_taken count_list_0_iff zero_enat_def)
          show ?thesis
            by (simp only: hcnt_lxs, subst h_lxs_eq, simp)
        qed
        have h_lys_cnt: \<open>count_llist lys x = count_llist (ldropn m lys) x\<close>
        proof -
          have heq_lys: \<open>lys = lappend (llist_of (ltaken m lys)) (ldropn m lys)\<close>
            by (rule ltaken_ldropn_decomp)
          show ?thesis
            by (subst heq_lys, simp only: count_llist_lappend lfinite_llist_of if_True,
                simp add: h_taken count_list_0_iff zero_enat_def)
        qed
        have h_inter_cnt: \<open>count_llist (linterleave lxs lys) x =
            eSuc (count_llist (linterleave (ldropn m lys) (ltl (ldropn m lxs))) x)\<close>
        proof -
          have heq: \<open>ldropWhile ((\<noteq>) x) (linterleave lxs lys) =
              LCons x (linterleave (ldropn m lys) (ltl (ldropn m lxs)))\<close>
            by (subst h_drop2, subst h_lxs_eq, simp)
          have h_tl: \<open>ltl (ldropWhile ((\<noteq>) x) (linterleave lxs lys)) =
              linterleave (ldropn m lys) (ltl (ldropn m lxs))\<close>
            by (simp add: heq)
          from count_llist_ctr(2)[OF hin] h_tl show ?thesis
            by simp
        qed
        show ?thesis
        proof (rule conjI)
          show \<open>(count_llist (linterleave lxs lys) x = 0) = (count_llist lxs x + count_llist lys x = 0)\<close>
            by (simp add: h_inter_cnt h_lxs_cnt)
        next
          show \<open>count_llist (linterleave lxs lys) x \<noteq> 0 \<longrightarrow> count_llist lxs x + count_llist lys x \<noteq> 0 \<longrightarrow>
            (\<exists>lxs' lys'. epred (count_llist (linterleave lxs lys) x) = count_llist (linterleave lxs' lys') x \<and>
                         epred (count_llist lxs x + count_llist lys x) = count_llist lxs' x + count_llist lys' x \<and>
                         \<not> lfinite lxs' \<and> \<not> lfinite lys') \<or>
            epred (count_llist (linterleave lxs lys) x) = epred (count_llist lxs x + count_llist lys x)\<close>
          proof (intro impI disjI1)
            show \<open>\<exists>lxs' lys'. epred (count_llist (linterleave lxs lys) x) = count_llist (linterleave lxs' lys') x \<and>
                         epred (count_llist lxs x + count_llist lys x) = count_llist lxs' x + count_llist lys' x \<and>
                         \<not> lfinite lxs' \<and> \<not> lfinite lys'\<close>
            proof (rule exI[of _ \<open>ldropn m lys\<close>], rule exI[of _ \<open>ltl (ldropn m lxs)\<close>], intro conjI)
              show \<open>epred (count_llist (linterleave lxs lys) x) = count_llist (linterleave (ldropn m lys) (ltl (ldropn m lxs))) x\<close>
                by (simp add: h_inter_cnt)
              show \<open>epred (count_llist lxs x + count_llist lys x) = count_llist (ldropn m lys) x + count_llist (ltl (ldropn m lxs)) x\<close>
                by (simp add: h_lxs_cnt h_lys_cnt iadd_Suc_right add.commute)
              show \<open>\<not> lfinite (ldropn m lys)\<close>
                using eq_enat by (simp add: linfinite_eq_not_lfinite)
              show \<open>\<not> lfinite (ltl (ldropn m lxs))\<close>
                using eq_enat by (simp add: linfinite_eq_not_lfinite)
            qed
          qed
        qed
      next
        case False
        have hodd: \<open>\<not> (\<exists>m. n = 2 * m)\<close> using False .
        have hm: \<open>n = 2 * (n div 2) + 1\<close>
          using hodd by arith
        have h_drop2: \<open>ldropWhile ((\<noteq>) x) (linterleave lxs lys) =
            linterleave (ldropn (n div 2) lys) (ldropn (Suc (n div 2)) lxs)\<close>
          using h_drop hodd eq_enat
          by (simp add: ldropn_linterleave linfinite_eq_not_lfinite)
        have h_hd_lys: \<open>lhd (ldropn (n div 2) lys) = x\<close>
        proof -
          have hnn: \<open>\<not> lnull (ldropn (n div 2) lys)\<close>
            using eq_enat by (metis linfinite_ldropn linfinite_not_lnull linfinite_eq_not_lfinite)
          have \<open>lhd (linterleave (ldropn (n div 2) lys) (ldropn (Suc (n div 2)) lxs)) =
              lhd (ldropn (n div 2) lys)\<close>
            by (cases \<open>ldropn (n div 2) lys\<close>) (use hnn in auto)
          with h_lhd h_drop2 show ?thesis by simp
        qed
        have h_taken: \<open>x \<notin> set (ltaken (Suc (n div 2)) lxs) \<and> x \<notin> set (ltaken (n div 2) lys)\<close>
        proof -
          have hlinf_lxs: \<open>linfinite lxs\<close> using eq_enat by (simp add: linfinite_eq_not_lfinite)
          have hlinf_lys: \<open>linfinite lys\<close> using eq_enat by (simp add: linfinite_eq_not_lfinite)
          have hlen: \<open>enat (Suc (2 * (n div 2))) = llength (ltakeWhile ((\<noteq>) x) (linterleave lxs lys))\<close>
            using h_len hm by simp
          from llength_ltakeWhile_linterleave_eq_Suc[OF hlinf_lxs hlinf_lys hlen] show ?thesis .
        qed
        have h_lys_eq: \<open>ldropn (n div 2) lys = LCons x (ltl (ldropn (n div 2) lys))\<close>
        proof -
          have hnn: \<open>\<not> lnull (ldropn (n div 2) lys)\<close>
            using eq_enat by (metis linfinite_ldropn linfinite_not_lnull linfinite_eq_not_lfinite)
          from lhd_LCons_ltl[OF hnn] h_hd_lys show ?thesis by simp
        qed
        have h_lys_cnt: \<open>count_llist lys x = eSuc (count_llist (ltl (ldropn (n div 2) lys)) x)\<close>
        proof -
          have heq: \<open>lys = lappend (llist_of (ltaken (n div 2) lys)) (ldropn (n div 2) lys)\<close>
            by (rule ltaken_ldropn_decomp)
          have hcnt: \<open>count_llist lys x = count_llist (ldropn (n div 2) lys) x\<close>
            by (subst heq, simp only: count_llist_lappend lfinite_llist_of if_True,
                simp add: h_taken count_list_0_iff zero_enat_def)
          show ?thesis
            by (simp only: hcnt, subst h_lys_eq, simp)
        qed
        have h_lxs_cnt: \<open>count_llist lxs x = count_llist (ldropn (Suc (n div 2)) lxs) x\<close>
        proof -
          have hx: \<open>x \<notin> set (ltaken (Suc (n div 2)) lxs)\<close> using h_taken by blast
          have heq: \<open>lxs = lappend (llist_of (ltaken (Suc (n div 2)) lxs)) (ldropn (Suc (n div 2)) lxs)\<close>
            by (rule ltaken_ldropn_decomp)
          have hA: \<open>count_llist (llist_of (ltaken (Suc (n div 2)) lxs)) x = 0\<close>
            by (simp del: ltaken.simps add: count_list_0_iff hx zero_enat_def)
          show ?thesis
            by (subst heq, simp only: count_llist_lappend lfinite_llist_of if_True hA add_0_left)
        qed
        have h_inter_cnt: \<open>count_llist (linterleave lxs lys) x =
            eSuc (count_llist (linterleave (ldropn (Suc (n div 2)) lxs) (ltl (ldropn (n div 2) lys))) x)\<close>
        proof -
          have heq: \<open>ldropWhile ((\<noteq>) x) (linterleave lxs lys) =
              LCons x (linterleave (ldropn (Suc (n div 2)) lxs) (ltl (ldropn (n div 2) lys)))\<close>
            by (subst h_drop2, subst h_lys_eq, simp)
          have h_tl: \<open>ltl (ldropWhile ((\<noteq>) x) (linterleave lxs lys)) =
              linterleave (ldropn (Suc (n div 2)) lxs) (ltl (ldropn (n div 2) lys))\<close>
            by (simp add: heq)
          from count_llist_ctr(2)[OF hin] h_tl show ?thesis
            by simp
        qed
        show ?thesis
        proof (rule conjI)
          show \<open>(count_llist (linterleave lxs lys) x = 0) = (count_llist lxs x + count_llist lys x = 0)\<close>
            by (simp add: h_inter_cnt h_lys_cnt)
        next
          show \<open>count_llist (linterleave lxs lys) x \<noteq> 0 \<longrightarrow> count_llist lxs x + count_llist lys x \<noteq> 0 \<longrightarrow>
            (\<exists>lxs' lys'. epred (count_llist (linterleave lxs lys) x) = count_llist (linterleave lxs' lys') x \<and>
                         epred (count_llist lxs x + count_llist lys x) = count_llist lxs' x + count_llist lys' x \<and>
                         \<not> lfinite lxs' \<and> \<not> lfinite lys') \<or>
            epred (count_llist (linterleave lxs lys) x) = epred (count_llist lxs x + count_llist lys x)\<close>
          proof (intro impI disjI1)
            show \<open>\<exists>lxs' lys'. epred (count_llist (linterleave lxs lys) x) = count_llist (linterleave lxs' lys') x \<and>
                         epred (count_llist lxs x + count_llist lys x) = count_llist lxs' x + count_llist lys' x \<and>
                         \<not> lfinite lxs' \<and> \<not> lfinite lys'\<close>
            proof (rule exI[of _ \<open>ldropn (Suc (n div 2)) lxs\<close>],
                   rule exI[of _ \<open>ltl (ldropn (n div 2) lys)\<close>], intro conjI)
              show \<open>epred (count_llist (linterleave lxs lys) x) = count_llist (linterleave (ldropn (Suc (n div 2)) lxs) (ltl (ldropn (n div 2) lys))) x\<close>
                by (simp add: h_inter_cnt)
              show \<open>epred (count_llist lxs x + count_llist lys x) = count_llist (ldropn (Suc (n div 2)) lxs) x + count_llist (ltl (ldropn (n div 2) lys)) x\<close>
                by (simp add: h_lxs_cnt h_lys_cnt iadd_Suc_right)
              show \<open>\<not> lfinite (ldropn (Suc (n div 2)) lxs)\<close>
                using eq_enat by (simp add: linfinite_eq_not_lfinite)
              show \<open>\<not> lfinite (ltl (ldropn (n div 2) lys))\<close>
                using eq_enat by (simp add: linfinite_eq_not_lfinite)
            qed
          qed
        qed
      qed
    qed
  qed
qed




lemma lfinite_linterleave[simp]: \<open>lfinite (linterleave lxs lys) \<longleftrightarrow> lfinite lxs \<and> lfinite lys\<close>
  by (metis enat_add_left_cancel llength_eq_infty_conv_lfinite llength_linterleave plus_enat_simps(3))

lift_definition cmadd :: \<open>'a cmset \<Rightarrow> 'a cmset \<Rightarrow> 'a cmset\<close> is linterleave
  by (auto simp: eq_cmset_def count_llist_linterleave)

lemma cmcount_cmadd[simp]: \<open>cmcount (cmadd M N) x = cmcount M x + cmcount N x\<close>
  by transfer (auto simp: count_llist_linterleave)

lemma count_llist_lmap: \<open>count_llist (lmap f lxs) b = isum (count_llist lxs) {a. f a = b}\<close>
proof -
  have h_ind: \<open>\<And>i. isum (\<lambda>a. if enat i < llength lxs \<and> lnth lxs i = a then 1 else 0) {a. f a = b} =
              (if enat i < llength lxs \<and> f (lnth lxs i) = b then 1 else 0)\<close>
  proof -
    fix i
    show \<open>isum (\<lambda>a. if enat i < llength lxs \<and> lnth lxs i = a then 1 else 0) {a. f a = b} =
          (if enat i < llength lxs \<and> f (lnth lxs i) = b then 1 else 0)\<close>
    proof (cases \<open>enat i < llength lxs \<and> f (lnth lxs i) = b\<close>)
      case True
      then have himem: \<open>lnth lxs i \<in> {a. f a = b}\<close> by simp
      have \<open>isum (\<lambda>a. if lnth lxs i = a then 1 else 0) {a. f a = b} =
                 isum (\<lambda>a. if lnth lxs i = a then 1 else 0) ({a. f a = b} - {lnth lxs i}) + 1\<close>
        by (subst insert_Diff[OF himem, symmetric], subst isum_insert) (auto simp: isum_eq_0_iff)
      also have \<open>isum (\<lambda>a. if lnth lxs i = a then 1 else 0) ({a. f a = b} - {lnth lxs i}) = 0\<close>
        by (auto simp: isum_eq_0_iff)
      finally show ?thesis using True by simp
    next
      case False
      then show ?thesis by (auto simp: isum_eq_0_iff)
    qed
  qed
  have step1: \<open>count_llist (lmap f lxs) b = isum (\<lambda>i. if enat i < llength lxs \<and> f (lnth lxs i) = b then 1 else 0) UNIV\<close>
    by (subst count_llist_isum, rule isum_cong) auto
  have step2: \<open>isum (count_llist lxs) {a. f a = b} =
    isum (\<lambda>i. if enat i < llength lxs \<and> f (lnth lxs i) = b then 1 else 0) UNIV\<close>
  proof -
    have \<open>isum (count_llist lxs) {a. f a = b} =
      isum (\<lambda>a. isum (\<lambda>i. if enat i < llength lxs \<and> lnth lxs i = a then 1 else 0) UNIV) {a. f a = b}\<close>
      by (rule isum_cong) (auto simp: count_llist_isum)
    also have \<open>\<dots> = isum (\<lambda>i. isum (\<lambda>a. if enat i < llength lxs \<and> lnth lxs i = a then 1 else 0) {a. f a = b}) UNIV\<close>
      by (rule isum_swap)
    also have \<open>\<dots> = isum (\<lambda>i. if enat i < llength lxs \<and> f (lnth lxs i) = b then 1 else 0) UNIV\<close>
    proof (rule isum_cong, simp)
      fix x
      show \<open>isum (\<lambda>a. if enat x < llength lxs \<and> lnth lxs x = a then 1 else 0) {a. f a = b} =
            (if enat x < llength lxs \<and> f (lnth lxs x) = b then 1 else 0)\<close>
        by (rule h_ind)
    qed
    finally show ?thesis .
  qed
  show ?thesis by (simp only: step1 step2)
qed

lemma cmcount_cmimage[simp]: \<open>cmcount (cmimage f M) b = isum (cmcount M) {a. f a = b}\<close>
  by transfer (simp add: count_llist_lmap)

lift_definition cminfinite :: \<open>'a cmset \<Rightarrow> bool\<close> is linfinite
  by (metis eq_cmset_def eq_cmset_llength linfinite_eq_llength)

lemma Sup_enat_eq_inf: \<open>Sup (A :: enat set) = \<infinity> \<longleftrightarrow> \<infinity> \<in> A \<or> infinite A\<close>
  by (auto simp: Sup_enat_def Max_eqI dest: Max_in)

lemma sum_eq_inf: \<open>finite A \<Longrightarrow> sum (f :: _ \<Rightarrow> enat) A = \<infinity> \<longleftrightarrow> (\<exists>a \<in> A. f a = \<infinity>)\<close>
  by (induct A rule: finite_induct) auto

lemma inf_eq_sum: \<open>finite A \<Longrightarrow> \<infinity> = sum (f :: _ \<Rightarrow> enat) A \<longleftrightarrow> (\<exists>a \<in> A. f a = \<infinity>)\<close>
  by (metis sum_eq_inf)

primcorec mk_chain where
  \<open>mk_chain A C = (let a = (SOME a. a \<in> A) in LCons C (mk_chain (A - {a}) (insert a C)))\<close>

lemma in_lset_mk_chainD: \<open>X \<in> lset (mk_chain A C) \<Longrightarrow> infinite A \<Longrightarrow> \<exists>B \<subseteq> A. finite B \<and> X = C \<union> B\<close>
proof (induct X \<open>mk_chain A C\<close> arbitrary: A C rule: llist.set_induct)
  case (LCons1 A C)
  then show ?case
    by (subst (asm) mk_chain.code) blast
next
  case (LCons2 x lxs X A C)
  let ?a = \<open>SOME a. a \<in> A\<close>
  have a_in_A: \<open>?a \<in> A\<close> using LCons2.prems by (auto simp: some_in_eq)
  have lxs_eq: \<open>lxs = mk_chain (A - {?a}) (insert ?a C)\<close>
    using LCons2.hyps(1,3) by (metis llist.inject mk_chain.code)
  have inf': \<open>infinite (A - {?a})\<close> using LCons2.prems by simp
  obtain B where B_sub: \<open>B \<subseteq> A - {?a}\<close> and B_fin: \<open>finite B\<close> and X_eq: \<open>X = insert ?a C \<union> B\<close>
    using LCons2.hyps(2)[unfolded lxs_eq, OF _ inf'] by blast
  show ?case using B_sub
    by (intro exI[of _ \<open>insert ?a B\<close>]) (auto simp: a_in_A B_fin X_eq)
qed

lemma linfinite_mk_chain[simp]: \<open>linfinite (mk_chain A C)\<close>
proof (coinduction arbitrary: A C)
  case (linfinite A C)
  then show ?case
    by (subst mk_chain.code) blast
qed

coinductive chain for R where
  \<open>chain R LNil\<close>
| \<open>chain R (LCons x LNil)\<close>
| \<open>R x y \<Longrightarrow> chain R (LCons y lxs) \<Longrightarrow> chain R (LCons x (LCons y lxs))\<close>

inductive_cases chain_LConsE: \<open>chain R (LCons x lxs)\<close>

lemma chain_mk_chain: \<open>infinite A \<Longrightarrow> A \<inter> C = {} \<Longrightarrow> chain (\<subset>) (mk_chain A C)\<close>
proof (coinduction arbitrary: A C)
  case (chain A C)
  let ?a = \<open>SOME a. a \<in> A\<close>
  have ha: \<open>?a \<in> A\<close>
    using \<open>infinite A\<close> infinite_imp_nonempty by (metis some_in_eq)
  have ha_notin: \<open>?a \<notin> C\<close>
    using \<open>A \<inter> C = {}\<close> ha by blast
  let ?a' = \<open>SOME a. a \<in> A - {?a}\<close>
  have expand1: \<open>mk_chain A C = LCons C (mk_chain (A - {?a}) (insert ?a C))\<close>
    by (subst mk_chain.code) simp
  have expand2: \<open>mk_chain (A - {?a}) (insert ?a C) =
      LCons (insert ?a C) (mk_chain (A - {?a} - {?a'}) (insert ?a' (insert ?a C)))\<close>
    by (subst mk_chain.code) simp
  show ?case
  proof (intro disjI2)
    show \<open>\<exists>x y lxs. mk_chain A C = LCons x (LCons y lxs) \<and> x \<subset> y \<and>
            ((\<exists>A C. LCons y lxs = mk_chain A C \<and> infinite A \<and> A \<inter> C = {}) \<or> chain (\<subset>) (LCons y lxs))\<close>
    proof (intro exI conjI)
      show \<open>mk_chain A C =
          LCons C (LCons (insert ?a C) (mk_chain (A - {?a} - {?a'}) (insert ?a' (insert ?a C))))\<close>
        by (simp only: expand1 expand2)
      show \<open>C \<subset> insert ?a C\<close>
        using ha_notin by blast
      show \<open>(\<exists>A' C'. LCons (insert ?a C) (mk_chain (A - {?a} - {?a'}) (insert ?a' (insert ?a C))) =
              mk_chain A' C' \<and> infinite A' \<and> A' \<inter> C' = {}) \<or>
            chain (\<subset>) (LCons (insert ?a C) (mk_chain (A - {?a} - {?a'}) (insert ?a' (insert ?a C))))\<close>
      proof (intro disjI1 exI conjI)
        show \<open>LCons (insert ?a C) (mk_chain (A - {?a} - {?a'}) (insert ?a' (insert ?a C))) =
            mk_chain (A - {?a}) (insert ?a C)\<close>
          by (rule expand2[symmetric])
        show \<open>infinite (A - {?a})\<close>
          using \<open>infinite A\<close> by simp
        show \<open>(A - {?a}) \<inter> (insert ?a C) = {}\<close>
          using \<open>A \<inter> C = {}\<close> ha by (auto simp: disjoint_iff)
      qed
    qed
  qed
qed

lemma chainD:
  \<open>chain R lxs \<Longrightarrow> enat (Suc i) < llength lxs \<Longrightarrow> R (lnth lxs i) (lnth lxs (Suc i))\<close>
proof (induct i arbitrary: lxs)
  case 0
  then show ?case by (auto simp add: zero_enat_def elim: chain.cases)
next
  case (Suc i)
  then show ?case by (fastforce simp add: zero_enat_def Suc_ile_eq elim: chain.cases)
qed

lemma chain_transD:
  assumes \<open>transp R\<close>
  shows \<open>chain R lxs \<Longrightarrow> i < j \<Longrightarrow> enat j < llength lxs \<Longrightarrow> R (lnth lxs i) (lnth lxs j)\<close>
proof (induct \<open>j - i\<close> arbitrary: i j lxs)
  case 0
  then show ?case by simp
next
  case (Suc x)
  note IH = Suc.hyps(1)
  show ?case
  proof (cases j)
    case 0
    with Suc.prems show ?thesis by simp
  next
    case (Suc j')
    show ?thesis
    proof (cases \<open>i < j'\<close>)
      case True
      have xeq: \<open>x = j' - i\<close> using Suc.hyps(2) Suc by simp
      have lt: \<open>enat j' < llength lxs\<close>
        using Suc.prems(3) Suc by (metis enat_ord_simps(2) lessI less_trans)
      have mid: \<open>R (lnth lxs i) (lnth lxs j')\<close>
        using IH[of j' i lxs] xeq Suc.prems(1) True lt by blast
      have step: \<open>R (lnth lxs j') (lnth lxs (Suc j'))\<close>
        using chainD[OF Suc.prems(1)] Suc.prems(3) Suc by (simp add: Suc_ile_eq)
      with mid show ?thesis using assms Suc unfolding transp_def by blast
    next
      case False
      then have \<open>i = j'\<close> using Suc.prems(2) Suc by simp
      with Suc show ?thesis
        using chainD[OF Suc.prems(1)] Suc.prems(3) by (simp add: Suc_ile_eq)
    qed
  qed
qed

lemma chain_cpo_chain: \<open>transp R \<Longrightarrow> chain R lxs \<Longrightarrow> Complete_Partial_Order.chain (reflclp R) (lset lxs)\<close>
  unfolding Complete_Partial_Order.chain_def in_lset_conv_lnth
  by (metis (full_types) chain_transD in_lset_conv_lnth linorder_cases sup2CI)

lemma reflclp_subset: \<open>reflclp (\<subset>) = (\<subseteq>)\<close>
  by auto

lemma sum_strict_mono2_enat:
  fixes f :: \<open>'a \<Rightarrow> enat\<close>
  assumes \<open>finite B\<close> \<open>A \<subseteq> B\<close> \<open>b \<in> B-A\<close> \<open>f b > 0\<close> \<open>\<infinity> \<notin> f ` B\<close>
  shows \<open>sum f A < sum f B\<close>
proof -
  have \<open>B - A \<noteq> {}\<close>
    using assms(3) by blast
  have \<open>sum f (B-A) > 0\<close>
    by (rule sum_pos2) (use assms in auto)
  moreover have \<open>sum f B = sum f (B-A) + sum f A\<close>
    by (rule sum.subset_diff) (use assms in auto)
  ultimately show ?thesis
    by (metis add.commute add_diff_cancel_enat assms(1,5) enat_le_plus_same(2) idiff_self image_iff nless_le sum_eq_inf)
qed

lemma infinite_lset_chain:
  assumes \<open>linfinite lxs\<close> \<open>chain R lxs\<close> \<open>irreflp R\<close> \<open>transp R\<close>
  shows \<open>infinite (lset lxs)\<close>
proof -
  have inj: \<open>inj_on (lnth lxs) UNIV\<close>
  proof (rule inj_onI)
    fix m n :: nat assume eq: \<open>lnth lxs m = lnth lxs n\<close>
    show \<open>m = n\<close>
    proof (rule antisym)
      show \<open>m \<le> n\<close>
      proof (rule ccontr)
        assume \<open>\<not> m \<le> n\<close>
        then have \<open>n < m\<close> by simp
        with assms have \<open>R (lnth lxs n) (lnth lxs m)\<close>
          using chain_transD[OF assms(4) assms(2)] linfinite_eq_llength
          by (metis enat_ord_code(4) assms(1))
        with assms(3) eq show False by (metis irreflpD)
      qed
    next
      show \<open>n \<le> m\<close>
      proof (rule ccontr)
        assume \<open>\<not> n \<le> m\<close>
        then have \<open>m < n\<close> by simp
        with assms have \<open>R (lnth lxs m) (lnth lxs n)\<close>
          using chain_transD[OF assms(4) assms(2)] linfinite_eq_llength
          by (metis enat_ord_code(4) assms(1))
        with assms(3) eq show False by (metis irreflpD)
      qed
    qed
  qed
  have \<open>infinite (lnth lxs ` UNIV)\<close>
    using finite_image_iff[OF inj] by simp
  with assms(1) show ?thesis
    by (auto simp: lset_conv_lnth linfinite_eq_llength full_SetCompr_eq)
qed

lemma isum_eq_inf: \<open>isum f A = \<infinity> \<longleftrightarrow> infinite {a \<in> A. f a \<noteq> 0} \<or> (\<exists>a \<in> A. f a = \<infinity>)\<close>
proof (rule iffI)
  assume h: \<open>isum f A = \<infinity>\<close>
  then have h2: \<open>\<infinity> \<in> sum f ` {B |B. B \<subseteq> A \<and> finite B} \<or> infinite (sum f ` {B |B. B \<subseteq> A \<and> finite B})\<close>
    unfolding isum_def Sup_enat_eq_inf by simp
  show \<open>infinite {a \<in> A. f a \<noteq> 0} \<or> (\<exists>a \<in> A. f a = \<infinity>)\<close>
  proof (rule ccontr)
    assume hc: \<open>\<not> (infinite {a \<in> A. f a \<noteq> 0} \<or> (\<exists>a \<in> A. f a = \<infinity>))\<close>
    then have hfin: \<open>finite {a \<in> A. f a \<noteq> 0}\<close> and hno_inf: \<open>\<forall>a \<in> A. f a \<noteq> \<infinity>\<close> by auto
    have surj: \<open>sum f ` {B |B. B \<subseteq> A \<and> finite B} \<subseteq> sum f ` Pow {a \<in> A. f a \<noteq> 0}\<close>
    proof
      fix s assume \<open>s \<in> sum f ` {B |B. B \<subseteq> A \<and> finite B}\<close>
      then obtain B where hB: \<open>B \<subseteq> A\<close> \<open>finite B\<close> and seq: \<open>s = sum f B\<close> by auto
      have eq: \<open>sum f B = sum f {a \<in> B. f a \<noteq> 0}\<close>
        by (rule sum.mono_neutral_right) (use hB in auto)
      show \<open>s \<in> sum f ` Pow {a \<in> A. f a \<noteq> 0}\<close>
        using hB eq seq by (auto simp: Pow_def)
    qed
    have \<open>finite (sum f ` {B |B. B \<subseteq> A \<and> finite B})\<close>
      by (rule finite_subset[OF surj]) (rule finite_imageI, rule finite_Pow_iff[THEN iffD2, OF hfin])
    moreover have \<open>\<infinity> \<notin> sum f ` {B |B. B \<subseteq> A \<and> finite B}\<close>
    proof
      assume \<open>\<infinity> \<in> sum f ` {B |B. B \<subseteq> A \<and> finite B}\<close>
      then obtain B where hB: \<open>B \<subseteq> A\<close> \<open>finite B\<close> and seq: \<open>sum f B = \<infinity>\<close> by auto
      then obtain a where ha: \<open>a \<in> B\<close> and hfa: \<open>f a = \<infinity>\<close>
        using inf_eq_sum[of B f] by auto
      have \<open>a \<in> A\<close> using ha hB(1) by auto
      with hfa hno_inf show False by auto
    qed
    ultimately show False using h2 by simp
  qed
next
  assume h: \<open>infinite {a \<in> A. f a \<noteq> 0} \<or> (\<exists>a \<in> A. f a = \<infinity>)\<close>
  show \<open>isum f A = \<infinity>\<close>
  proof (cases \<open>\<exists>a \<in> A. f a = \<infinity>\<close>)
    case True
    then obtain a where ha: \<open>a \<in> A\<close> and hfa: \<open>f a = \<infinity>\<close> by auto
    have \<open>\<infinity> \<in> sum f ` {B |B. B \<subseteq> A \<and> finite B}\<close>
      by (rule image_eqI[where x=\<open>{a}\<close>]) (simp_all add: ha hfa)
    then show ?thesis unfolding isum_def Sup_enat_eq_inf by simp
  next
    case False
    with h have hinf: \<open>infinite {a \<in> A. f a \<noteq> 0}\<close> and hno_inf: \<open>\<infinity> \<notin> f ` A\<close> by auto
    show ?thesis
    proof -
      let ?Q = \<open>{a \<in> A. f a \<noteq> 0}\<close>
      let ?\<AA> = \<open>lset (mk_chain ?Q {})\<close>
      have h_chain_strict: \<open>chain (\<subset>) (mk_chain ?Q {})\<close>
        by (rule chain_mk_chain) (use hinf in simp_all)
      have h_chain: \<open>Complete_Partial_Order.chain (\<subseteq>) ?\<AA>\<close>
        by (rule chain_cpo_chain[of \<open>(\<subset>)\<close>, unfolded reflclp_subset])
           (simp, rule h_chain_strict)
      have h_inf_\<AA>: \<open>infinite ?\<AA>\<close>
        by (rule infinite_lset_chain[where R=\<open>(\<subset>)\<close>])
           (rule linfinite_mk_chain, rule h_chain_strict, simp_all)
      have h_sub_\<AA>: \<open>\<forall>C \<in> ?\<AA>. C \<subseteq> ?Q\<close>
        by (auto dest!: in_lset_mk_chainD[OF _ hinf])
      have h_mem_\<AA>: \<open>\<forall>C \<in> ?\<AA>. C \<in> {B |B. B \<subseteq> A \<and> finite B}\<close>
        by (auto dest!: in_lset_mk_chainD[OF _ hinf])
      have h_inj: \<open>inj_on (sum f) ?\<AA>\<close>
      proof (rule inj_onI)
        fix B C assume hB: \<open>B \<in> ?\<AA>\<close> and hC: \<open>C \<in> ?\<AA>\<close> and heq: \<open>sum f B = sum f C\<close>
        from h_chain have chain_rel: \<open>\<forall>B \<in> ?\<AA>. \<forall>C \<in> ?\<AA>. B \<subseteq> C \<or> C \<subseteq> B\<close>
          unfolding Complete_Partial_Order.chain_def by auto
        from chain_rel[rule_format, OF hB hC] have \<open>B \<subseteq> C \<or> C \<subseteq> B\<close> .
        moreover {
          assume hBC: \<open>B \<subset> C\<close>
          from h_mem_\<AA>[rule_format, OF hC] have hCA: \<open>C \<subseteq> A\<close> and hfinC: \<open>finite C\<close> by simp+
          from h_mem_\<AA>[rule_format, OF hB] have hfinB: \<open>finite B\<close> by simp+
          obtain c where hcC: \<open>c \<in> C - B\<close> using hBC by auto
          have hfcpos: \<open>0 < f c\<close>
            using hcC h_sub_\<AA>[rule_format, OF hC] by (auto simp: zero_less_iff_neq_zero)
          have hno_infC: \<open>\<infinity> \<notin> f ` C\<close> using hCA hno_inf by auto
          have \<open>sum f B < sum f C\<close>
            using sum_strict_mono2_enat[where B=C and A=B and b=c and f=f,
                    OF hfinC _ hcC hfcpos hno_infC]
            using hBC by auto
          with heq have False by simp
        }
        moreover {
          assume hCB: \<open>C \<subset> B\<close>
          from h_mem_\<AA>[rule_format, OF hB] have hBA: \<open>B \<subseteq> A\<close> and hfinB: \<open>finite B\<close> by simp+
          from h_mem_\<AA>[rule_format, OF hC] have hCA: \<open>C \<subseteq> A\<close> and hfinC: \<open>finite C\<close> by simp+
          obtain c where hcB: \<open>c \<in> B - C\<close> using hCB by auto
          have hfcpos: \<open>0 < f c\<close>
            using hcB h_sub_\<AA>[rule_format, OF hB] by (auto simp: zero_less_iff_neq_zero)
          have hno_infB: \<open>\<infinity> \<notin> f ` B\<close> using hBA hno_inf by auto
          have \<open>sum f C < sum f B\<close>
            using sum_strict_mono2_enat[where B=B and A=C and b=c and f=f,
                    OF hfinB _ hcB hfcpos hno_infB]
            using hCB by auto
          with heq have False by simp
        }
        ultimately show \<open>B = C\<close> by (cases \<open>B = C\<close>) auto
      qed
      have h_inf_image: \<open>infinite (sum f ` ?\<AA>)\<close>
        by (metis finite_imageD h_inj h_inf_\<AA>)
      have \<open>sum f ` ?\<AA> \<subseteq> sum f ` {B |B. B \<subseteq> A \<and> finite B}\<close>
        using h_mem_\<AA> by auto
      from infinite_super[OF this h_inf_image]
      show ?thesis unfolding isum_def Sup_enat_eq_inf by simp
    qed
  qed
qed

lemma cminfinite_alt: \<open>cminfinite M = ((\<exists>x. cmcount M x = \<infinity>) \<or> infinite {x. cmcount M x \<noteq> 0})\<close>
proof (transfer)
  fix M :: \<open>'a llist\<close>
  show \<open>linfinite M = ((\<exists>x. count_llist M x = \<infinity>) \<or> infinite {x. count_llist M x \<noteq> 0})\<close>
  proof (cases \<open>lfinite M\<close>)
    case True
    then have \<open>\<not> linfinite M\<close> by (simp add: linfinite_eq_not_lfinite)
    moreover have \<open>\<forall>x. count_llist M x \<noteq> \<infinity>\<close>
      using True
    proof (induct M rule: lfinite.induct)
      case lfinite_LNil
      then show ?case by simp
    next
      case (lfinite_LConsI a M')
      then show ?case
        by (auto simp: eSuc_eq_infinity_iff eSuc_enat dest!: spec[of _ M'] split: if_splits)
    qed
    moreover have \<open>finite {x. count_llist M x \<noteq> 0}\<close>
      using True
    proof (induct M rule: lfinite.induct)
      case lfinite_LNil
      then show ?case by simp
    next
      case (lfinite_LConsI a M')
      then have \<open>{x. count_llist (LCons M' a) x \<noteq> 0} \<subseteq> insert M' {x. count_llist a x \<noteq> 0}\<close>
        by auto
      with lfinite_LConsI(2) show ?case
        by (meson finite_insert rev_finite_subset)
    qed
    ultimately show ?thesis by simp
  next
    case False
    then have linf: \<open>linfinite M\<close> by (simp add: linfinite_eq_not_lfinite)
    have count_inf: \<open>count_llist (lmap (\<lambda>_. undefined) M) undefined = \<infinity>\<close>
      using False by (simp add: count_llist_lmap_const llength_eq_infty_conv_lfinite)
    then have \<open>(\<exists>x. count_llist M x = \<infinity>) \<or> infinite {a \<in> UNIV. count_llist M a \<noteq> 0}\<close>
      unfolding count_llist_lmap isum_eq_inf by fastforce
    with linf show ?thesis by simp
  qed
qed

lemma cmset_alt: \<open>cmset M = {a. cmcount M a \<noteq> 0}\<close>
proof (transfer)
  fix M :: \<open>'a llist\<close>
  show \<open>(\<Inter>(mx :: (unit + 'a) llist)\<in>Collect (eq_cmset (lmap Inr M)). \<Union> (Basic_BNFs.setr ` lset mx)) = {a. count_llist M a \<noteq> 0}\<close>
  proof -
    { fix x
      assume \<open>\<forall>xa. (\<forall>x. count_llist (lmap Inr M) x = count_llist xa x) \<longrightarrow> (\<exists>xa\<in>lset xa. x \<in> Basic_BNFs.setr xa)\<close>
      then have \<open>x \<in> lset M\<close> by force
    }
    moreover
    { fix x :: 'a and lxs :: \<open>(unit + 'a) llist\<close>
      assume \<open>x \<in> lset M\<close> and \<open>\<forall>x. count_llist (lmap Inr M) x = count_llist lxs x\<close>
      then have \<open>\<exists>z\<in>lset lxs. x \<in> Basic_BNFs.setr z\<close>
        by (metis count_llist_zero_iff imageI lset_lmap setr.intros)
    }
    ultimately show ?thesis
      by (fastforce simp: count_llist_zero_iff eq_cmset_def)
  qed
qed

lift_definition cmconst :: \<open>'a \<Rightarrow> 'a cmset\<close> is \<open>repeat\<close> .

lemma cminfinite_cmconst[simp]: \<open>cminfinite (cmconst a)\<close>
  by transfer (auto simp: linfinite_eq_not_lfinite)

lemma cminfinite_cmimage: \<open>cminfinite (cmimage f M) \<longleftrightarrow> cminfinite M\<close>
  by transfer (auto simp: linfinite_eq_not_lfinite)


locale cmset_as_Quotient
begin

setup_lifting Quotient_cmset

declare cmempty.transfer[transfer_rule]
declare cmadd.transfer[transfer_rule]
declare cmset.map_transfer[transfer_rule]
declare cmset.set_transfer[transfer_rule]
declare cminfinite.transfer[transfer_rule]

end

locale cmset_as_typedef
begin

setup_lifting type_definition_cmset

lemma cmempty_transfer[transfer_rule]: \<open>pcr_cmset R (\<lambda>_. 0) cmempty\<close>
  by (auto simp: pcr_cmset_def cr_cmset_def rel_fun_def relcompp_apply)

lemma cmadd_transfer[transfer_rule]: \<open>rel_fun (pcr_cmset R) (rel_fun (pcr_cmset R) (pcr_cmset R)) (\<lambda>M N x. M x + N x) cmadd\<close>
  by (auto simp: pcr_cmset_def cr_cmset_def rel_fun_def relcompp_apply)

lemma cmimage_transfer[transfer_rule]: \<open>rel_fun (=) (rel_fun (pcr_cmset (=)) (pcr_cmset (=))) (\<lambda>f M b. isum M {a. f a = b}) cmimage\<close>
  by (auto simp: pcr_cmset_def cr_cmset_def rel_fun_def relcompp_apply intro: isum_cong)

lemma cmset_transfer[transfer_rule]: \<open>rel_fun (pcr_cmset (=)) (=) (\<lambda>M. {a. M a \<noteq> 0}) cmset\<close>
  by (auto simp: pcr_cmset_def cr_cmset_def rel_fun_def cmset_alt)

lemma cminfinite_transfer[transfer_rule]: \<open>rel_fun (pcr_cmset (=)) (=) (\<lambda>M. (\<exists>x. M x = \<infinity>) \<or> infinite {x. M x \<noteq> 0}) cminfinite\<close>
  by (auto simp: pcr_cmset_def cr_cmset_def rel_fun_def cminfinite_alt)

lift_definition cmreplace :: \<open>'a cmset \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a cmset\<close> is
  \<open>\<lambda>f a b. f(a := epred (f a), b := eSuc (f b))\<close>
  by (erule countable_subset[rotated, OF countable_insert]) auto

lemma cminfinite_cmreplace: \<open>cminfinite M \<Longrightarrow> cminfinite (cmreplace M a b)\<close>
proof (transfer fixing: a b)
  fix M :: \<open>'a \<Rightarrow> enat\<close>
  assume M: \<open>countable {x. M x \<noteq> 0}\<close> \<open>(\<exists>x. M x = \<infinity>) \<or> infinite {x. M x \<noteq> 0}\<close>
  show \<open>(\<exists>x. (M(a := epred (M a), b := eSuc (M b))) x = \<infinity>) \<or> infinite {x. (M(a := epred (M a), b := eSuc (M b))) x \<noteq> 0}\<close>
  proof (cases \<open>\<exists>x. M x = \<infinity>\<close>)
    case True
    then obtain x where \<open>M x = \<infinity>\<close> ..
    show ?thesis
      by (metis \<open>M x = \<infinity>\<close> eSuc_infinity epred_Infty fun_upd_other fun_upd_same)
  next
    case False
    with M have \<open>infinite {x. M x \<noteq> 0}\<close> by blast
    then have \<open>infinite {x. (M(a := epred (M a), b := eSuc (M b))) x \<noteq> 0}\<close>
      by (rule contrapos_nn, elim finite_subset[rotated, OF finite_insert[THEN iffD2, of _ a]]) auto
    then show ?thesis
      by blast
  qed
qed
end

lifting_update cmset.lifting
lifting_forget cmset.lifting

end