(*  Title:      HOL/Library/Coinductive_Stream.thy
    Author:     Peter Gammie and Andreas Lochbihler
*)
header {* Coinductive streams *}

theory Coinductive_Stream
imports
  "~~/src/HOL/BNF_Examples/Stream"
  Coinductive_List
begin

lemma invariantI: "P x \<Longrightarrow> Lifting.invariant P x x"
by(simp add: Lifting.invariant_def)

primcorec unfold_stream :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b stream" where
  "unfold_stream g1 g2 a = g1 a ## unfold_stream g1 g2 (g2 a)"

text {*
  The following setup should be done by the BNF package.
*}

declare stream.corec [code]

text {* congruence rule *}

declare stream.map_cong [cong]

text {* lemmas about generated constants *}

lemma eq_SConsD: "xs = SCons y ys \<Longrightarrow> shd xs = y \<and> stl xs = ys"
by auto

lemma smap_ident [simp]: "smap (\<lambda>x. x) xs = xs"
by(simp only: id_def[symmetric] stream.map_id)

lemma smap_eq_SCons_conv:
  "smap f xs = y ## ys \<longleftrightarrow> 
  (\<exists>x xs'. xs = x ## xs' \<and> y = f x \<and> ys = smap f xs')"
by(cases xs)(auto)

lemma smap_id: 
  "smap id = id"
by(simp add: fun_eq_iff stream.map_id)

lemma smap_unfold_stream:
  "smap f (unfold_stream SHD STL b) = unfold_stream (f \<circ> SHD) STL b"
by(coinduction arbitrary: b) auto

lemma smap_corec_stream:
  "smap f (corec_stream SHD endORmore STL_end STL_more b) =
   corec_stream (f \<circ> SHD) endORmore (smap f \<circ> STL_end) STL_more b"
by(coinduction arbitrary: b rule: stream.strong_coinduct) auto

lemma unfold_stream_ltl_unroll:
  "unfold_stream SHD STL (STL b) = unfold_stream (SHD \<circ> STL) STL b"
by(coinduction arbitrary: b) auto

lemma unfold_stream_eq_Stream [simp]:
  "unfold_stream SHD STL b = x ## xs \<longleftrightarrow>
  x = SHD b \<and> xs = unfold_stream SHD STL (STL b)"
by(subst unfold_stream.ctr) auto

lemma unfold_stream_id [simp]: "unfold_stream shd stl xs = xs"
by(coinduction arbitrary: xs) simp_all

lemma sset_neq_empty [simp]: "sset xs \<noteq> {}"
by(cases xs) simp_all

lemmas shd_in_sset [simp] = shd_sset

lemma sset_stl: "sset (stl xs) \<subseteq> sset xs"
by(cases xs) auto

lemmas in_sset_stlD = stl_sset

text {* induction rules *}

theorems stream_set_induct = sset_induct1

subsection {* Lemmas about operations from @{theory Stream} *}

lemma szip_iterates:
  "szip (siterate f a) (siterate g b) = siterate (map_prod f g) (a, b)"
by(coinduction arbitrary: a b) auto

lemma szip_smap1: "szip (smap f xs) ys = smap (apfst f) (szip xs ys)"
by(coinduction arbitrary: xs ys) auto

lemma szip_smap2: "szip xs (smap g ys) = smap (apsnd g) (szip xs ys)"
by(coinduction arbitrary: xs ys) auto

lemma szip_smap [simp]: "szip (smap f xs) (smap g ys) = smap (map_prod f g) (szip xs ys)"
by(coinduction arbitrary: xs ys) auto

lemma smap_fst_szip [simp]: "smap fst (szip xs ys) = xs"
by(coinduction arbitrary: xs ys) auto

lemma smap_snd_szip [simp]: "smap snd (szip xs ys) = ys"
by(coinduction arbitrary: xs ys) auto

lemma snth_shift: "snth (shift xs ys) n = (if n < length xs then xs ! n else snth ys (n - length xs))"
by simp

declare szip_unfold [simp, nitpick_simp]

lemma szip_shift: 
  "length xs = length us
  \<Longrightarrow> szip (xs @- ys) (us @- zs) = zip xs us @- szip ys zs"
by(induct xs arbitrary: us)(auto simp add: Suc_length_conv)


subsection {* Link @{typ "'a stream"} to @{typ "'a llist"} *}

definition llist_of_stream :: "'a stream \<Rightarrow> 'a llist"
where "llist_of_stream = unfold_llist (\<lambda>_. False) shd stl"

definition stream_of_llist :: "'a llist \<Rightarrow> 'a stream"
where "stream_of_llist = unfold_stream lhd ltl"

lemma lnull_llist_of_stream [simp]: "\<not> lnull (llist_of_stream xs)"
by(simp add: llist_of_stream_def)

lemma ltl_llist_of_stream [simp]: "ltl (llist_of_stream xs) = llist_of_stream (stl xs)"
by(simp add: llist_of_stream_def)

lemma stl_stream_of_llist [simp]: "stl (stream_of_llist xs) = stream_of_llist (ltl xs)"
by(simp add: stream_of_llist_def)

lemma shd_stream_of_llist [simp]: "shd (stream_of_llist xs) = lhd xs"
by(simp add: stream_of_llist_def)

lemma lhd_llist_of_stream [simp]: "lhd (llist_of_stream xs) = shd xs"
by(simp add: llist_of_stream_def)

lemma stream_of_llist_llist_of_stream [simp]: 
  "stream_of_llist (llist_of_stream xs) = xs"
by(coinduction arbitrary: xs) simp_all

lemma llist_of_stream_stream_of_llist [simp]:
  "\<not> lfinite xs \<Longrightarrow> llist_of_stream (stream_of_llist xs) = xs"
by(coinduction arbitrary: xs) auto

lemma lfinite_llist_of_stream [simp]: "\<not> lfinite (llist_of_stream xs)"
proof
  assume "lfinite (llist_of_stream xs)"
  thus False
    by(induct "llist_of_stream xs" arbitrary: xs rule: lfinite_induct) auto
qed

lemma stream_from_llist: "type_definition llist_of_stream stream_of_llist {xs. \<not> lfinite xs}"
by(unfold_locales) simp_all

interpretation stream!: type_definition llist_of_stream stream_of_llist "{xs. \<not> lfinite xs}"
by(fact stream_from_llist)

setup_lifting (no_code) stream_from_llist

lemma cr_streamI: "\<not> lfinite xs \<Longrightarrow> cr_stream xs (stream_of_llist xs)"
by(simp add: cr_stream_def Abs_stream_inverse)

lemma llist_of_stream_unfold_stream [simp]: 
  "llist_of_stream (unfold_stream SHD STL x) = unfold_llist (\<lambda>_. False) SHD STL x"
by(coinduction arbitrary: x) auto

lemma llist_of_stream_corec_stream [simp]:
  "llist_of_stream (corec_stream SHD endORmore STL_more STL_end x) =
   corec_llist (\<lambda>_. False) SHD endORmore (llist_of_stream \<circ> STL_more) STL_end x"
by(coinduction arbitrary: x rule: llist.strong_coinduct) auto

lemma LCons_llist_of_stream [simp]: "LCons x (llist_of_stream xs) = llist_of_stream (x ## xs)"
by(rule sym)(simp add: llist_of_stream_def)

lemma lmap_llist_of_stream [simp]:
  "lmap f (llist_of_stream xs) = llist_of_stream (smap f xs)"
by(coinduction arbitrary: xs) auto

lemma lset_llist_of_stream [simp]: "lset (llist_of_stream xs) = sset xs" (is "?lhs = ?rhs")
proof(intro set_eqI iffI)
  fix x
  assume "x \<in> ?lhs"
  thus "x \<in> ?rhs"
    by(induct "llist_of_stream xs" arbitrary: xs rule: llist_set_induct)(auto dest: in_sset_stlD)
next
  fix x
  assume "x \<in> ?rhs"
  thus "x \<in> ?lhs"
  proof(induct)
    case (shd xs)
    thus ?case using lhd_in_lset[of "llist_of_stream xs"] by simp
  next
    case stl 
    thus ?case
      by(auto simp add: ltl_llist_of_stream[symmetric] simp del: ltl_llist_of_stream dest: in_lset_ltlD)
  qed
qed

lemma lnth_list_of_stream [simp]:
  "lnth (llist_of_stream xs) = snth xs"
proof
  fix n
  show "lnth (llist_of_stream xs) n = snth xs n"
    by(induction n arbitrary: xs)(simp_all add: lnth_0_conv_lhd lnth_ltl[symmetric])
qed

lemma llist_of_stream_siterates [simp]: "llist_of_stream (siterate f x) = iterates f x"
by(coinduction arbitrary: x) auto

lemma lappend_llist_of_stream_conv_shift [simp]:
  "lappend (llist_of xs) (llist_of_stream ys) = llist_of_stream (xs @- ys)"
by(induct xs) simp_all

lemma lzip_llist_of_stream [simp]:
  "lzip (llist_of_stream xs) (llist_of_stream ys) = llist_of_stream (szip xs ys)"
by(coinduction arbitrary: xs ys) auto

context
begin
interpretation lifting_syntax .

lemma lmap_infinite_transfer [transfer_rule]:
  "(op = ===> Lifting.invariant (\<lambda>xs. \<not> lfinite xs) ===> Lifting.invariant (\<lambda>xs. \<not> lfinite xs)) lmap lmap"
by(simp add: fun_rel_def Lifting.invariant_def)

lemma lset_infinite_transfer [transfer_rule]:
  "(Lifting.invariant (\<lambda>xs. \<not> lfinite xs) ===> op =) lset lset"
by(simp add: fun_rel_def Lifting.invariant_def)

lemma unfold_stream_transfer [transfer_rule]:
  "(op = ===> op = ===> op = ===> pcr_stream op =) (unfold_llist (\<lambda>_. False)) unfold_stream"
by(auto simp add: stream.pcr_cr_eq cr_stream_def intro!: fun_relI)

lemma corec_stream_transfer [transfer_rule]:
  "(op = ===> op = ===> (op = ===> pcr_stream op =) ===> op = ===> op = ===> pcr_stream op=)
   (corec_llist (\<lambda>_. False)) corec_stream"
apply(auto intro!: fun_relI simp add: cr_stream_def stream.pcr_cr_eq)
apply(rule fun_cong) back
apply(rule_tac x=yc in fun_cong)
apply(rule_tac x=xb in arg_cong)
apply(auto elim: fun_relE)
done

lemma shd_transfer [transfer_rule]: "(pcr_stream A ===> A) lhd shd"
by(auto simp add: pcr_stream_def cr_stream_def intro!: fun_relI relcomppI)(frule llist_all2_lhdD, auto dest: llist_all2_lnullD)

lemma stl_transfer [transfer_rule]: "(pcr_stream A ===> pcr_stream A) ltl stl"
by(auto simp add: pcr_stream_def cr_stream_def intro!: fun_relI relcomppI dest: llist_all2_ltlI)

lemma llist_of_stream_transfer [transfer_rule]: "(pcr_stream op = ===> op =) id llist_of_stream"
by(simp add: fun_rel_def stream.pcr_cr_eq cr_stream_def)

lemma stream_of_llist_transfer [transfer_rule]: 
  "(Lifting.invariant (\<lambda>xs. \<not> lfinite xs) ===> pcr_stream op =) (\<lambda>xs. xs) stream_of_llist"
by(simp add: Lifting.invariant_def fun_rel_def stream.pcr_cr_eq cr_stream_def)

lemma Stream_transfer [transfer_rule]:
  "(A ===> pcr_stream A ===> pcr_stream A) LCons op ##"
by(auto simp add: cr_stream_def pcr_stream_def intro!: fun_relI relcomppI intro: llist_all2_expand)

lemma sset_transfer [transfer_rule]: "(pcr_stream A ===> rel_set A) lset sset"
by(auto 4 3 simp add: pcr_stream_def cr_stream_def intro!: fun_relI relcomppI rel_setI dest: llist_all2_lsetD1 llist_all2_lsetD2)

lemma smap_transfer [transfer_rule]:
  "((A ===> B) ===> pcr_stream A ===> pcr_stream B) lmap smap"
by(auto simp add: cr_stream_def pcr_stream_def intro!: fun_relI relcomppI dest: lmap_transfer[THEN fun_relD] elim: fun_relD)

lemma snth_transfer [transfer_rule]: "(pcr_stream op = ===> op =) lnth snth"
by(rule fun_relI)(clarsimp simp add: stream.pcr_cr_eq cr_stream_def fun_eq_iff)

lemma siterate_transfer [transfer_rule]: 
  "(op = ===> op = ===> pcr_stream op =) iterates siterate"
by(rule fun_relI)+(clarsimp simp add: stream.pcr_cr_eq cr_stream_def)

context
  fixes xs
  assumes inf: "\<not> lfinite xs"
  notes [transfer_rule] = invariantI[where P="\<lambda>xs. \<not> lfinite xs", OF inf]  
begin

lemma smap_stream_of_llist [simp]:
  shows "smap f (stream_of_llist xs) = stream_of_llist (lmap f xs)"
by transfer simp

lemma sset_stream_of_llist [simp]:
  assumes "\<not> lfinite xs"
  shows "sset (stream_of_llist xs) = lset xs"
by transfer simp        

end

lemma llist_all2_llist_of_stream [simp]: 
  "llist_all2 P (llist_of_stream xs) (llist_of_stream ys) = stream_all2 P xs ys"
apply(cases xs, cases ys)
apply(simp add: llist_all2_def stream_all2_def)
apply(safe elim!: GrpE)
 apply(rule_tac b="stream_of_llist b" in relcomppI)
  apply(auto intro!: GrpI)[2]
apply(rule_tac b="llist_of_stream b" in relcomppI)
 apply(auto intro!: GrpI)
done

lemma stream_all2_transfer [transfer_rule]:
  "(op = ===> pcr_stream op = ===> pcr_stream op = ===> op =) llist_all2 stream_all2"
by(simp add: fun_rel_def stream.pcr_cr_eq cr_stream_def)

lemma stream_all2_coinduct:
  assumes "X xs ys"
  and "\<And>xs ys. X xs ys \<Longrightarrow> P (shd xs) (shd ys) \<and> (X (stl xs) (stl ys) \<or> stream_all2 P (stl xs) (stl ys))"
  shows "stream_all2 P xs ys"
using assms
apply transfer
apply(rule_tac X="\<lambda>xs ys. \<not> lfinite xs \<and> \<not> lfinite ys \<and> X xs ys" in llist_all2_coinduct)
apply auto
done

lemma shift_transfer [transfer_rule]:
  "(op = ===> pcr_stream op = ===> pcr_stream op =) (lappend \<circ> llist_of) shift"
by(clarsimp simp add: fun_rel_def stream.pcr_cr_eq cr_stream_def)

lemma szip_transfer [transfer_rule]:
  "(pcr_stream op = ===> pcr_stream op = ===> pcr_stream op =) lzip szip"
by(simp add: stream.pcr_cr_eq cr_stream_def fun_rel_def)

subsection {* Link @{typ "'a stream"} with @{typ "nat \<Rightarrow> 'a"} *}

lift_definition of_seq :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a stream" is "inf_llist" by simp

lemma of_seq_rec [code]: "of_seq f = f 0 ## of_seq (f \<circ> Suc)"
by transfer (subst inf_llist_rec, simp add: o_def)

lemma snth_of_seq [simp]: "snth (of_seq f) = f"
by transfer (simp add: fun_eq_iff)

lemma snth_Stream: "snth (x ## xs) n = (case n of 0 \<Rightarrow> x | Suc n' \<Rightarrow> snth xs n')"
by(simp split: nat.split)

lemma snth_Stream_simps [simp]:
  shows snth_Stream_0: "(x ## xs) !! 0 = x"
  and snth_Stream_Suc: "(x ## xs) !! Suc n = xs !! n"
by(simp_all add: snth_Stream)

lemma of_seq_snth [simp]: "of_seq (snth xs) = xs"
by transfer simp

lemma shd_of_seq [simp]: "shd (of_seq f) = f 0"
by transfer simp

lemma stl_of_seq [simp]: "stl (of_seq f) = of_seq (\<lambda>n. f (Suc n))"
by transfer simp

lemma sset_of_seq [simp]: "sset (of_seq f) = range f"
by transfer simp

lemma smap_of_seq [simp]: "smap f (of_seq g) = of_seq (f \<circ> g)"
by transfer simp


subsection{* Function iteration @{const siterate}  and @{term sconst} *}

lemmas siterate [nitpick_simp] = siterate.code

lemma smap_iterates: "smap f (siterate f x) = siterate f (f x)"
by transfer (rule lmap_iterates)

lemma siterate_smap: "siterate f x = SCons x (smap f (siterate f x))"
by transfer (rule iterates_lmap)

lemma siterate_conv_of_seq: "siterate f a = of_seq (\<lambda>n. (f ^^ n) a)"
by transfer (rule iterates_conv_inf_llist)

lemma sconst_conv_of_seq: "sconst a = of_seq (\<lambda>_. a)"
by(simp add: siterate_conv_of_seq)

lemma szip_sconst1 [simp]: "szip (sconst a) xs = smap (Pair a) xs"
by(coinduction arbitrary: xs) auto

lemma szip_sconst2 [simp]: "szip xs (sconst b) = smap (\<lambda>x. (x, b)) xs"
by(coinduction arbitrary: xs) auto

end

end
