(*  Title:      HOL/Library/Coinductive_Stream.thy
    Author:     Peter Gammie and Andreas Lochbihler
*)
header {* Coinductive streams *}

theory Coinductive_Stream
imports
  Quotient_Coinductive_List
  "~~/src/HOL/Library/Quotient_Product"
  "~~/src/HOL/Library/Quotient_Set"
begin

lemma id_power: "id ^^ n = id"
by(induct n) auto

subsection {* Type definition *}

codata 'a stream = SCons (shd: 'a) (stl: "'a stream")

text {* 
  The following setup should be done by the BNF package.
*}

translations -- "poor man's case syntax"
  "case p of XCONST SCons x l \<Rightarrow> b" \<rightleftharpoons> "CONST stream_case (\<lambda>x l. b) p"
  "case p of (XCONST LCons :: 'b) x l \<Rightarrow> b" \<rightharpoonup> "CONST stream_case (\<lambda>x l. b) p"

text {* split rules without eta expansion *}

lemma stream_split: (* eta-contract stream.split *)
  "P (stream_case f stream) \<longleftrightarrow> 
  (\<forall>x1 x2. stream = SCons x1 x2 \<longrightarrow> P (f x1 x2))"
by(rule stream.split)

lemma stream_split_asm: (* eta-contracct stream.split_asm *)
  "P (stream_case f stream) \<longleftrightarrow>
   \<not> (\<exists>x1 x2. stream = SCons x1 x2 \<and> \<not> P (f x1 x2))"
by(rule stream.split_asm)

lemmas stream_splits = stream_split stream_split_asm

text {* congruence rules *}

lemma stream_map_cong [cong]:
  "\<lbrakk> xs = ys; \<And>x. x \<in> stream_set xs \<Longrightarrow> f x = g x \<rbrakk> \<Longrightarrow> stream_map f xs = stream_map g ys"
by clarify(rule stream.map_cong)

lemma stream_case_cong:
  "\<lbrakk> xs = ys; \<And>y ys'. ys = SCons y ys' \<Longrightarrow> f y ys' = g y ys' \<rbrakk>
  \<Longrightarrow> stream_case f xs = stream_case g ys"
by(cases xs) auto

lemma stream_case_weak_cong [cong]:
  "xs = ys \<Longrightarrow> stream_case f xs = stream_case f ys"
by simp

text {* Code generator setup *}

code_datatype SCons

lemma stream_case_code [code]: 
  "stream_case d (SCons M N) = d M N"
by simp_all

lemma stream_case_cert:
  assumes "CASE \<equiv> stream_case d"
  shows "CASE (SCons M N) \<equiv> d M N"
  using assms by simp

setup {*
  Code.add_case @{thm stream_case_cert}
*}

instantiation stream :: (equal) equal begin
definition equal_stream :: "'a stream \<Rightarrow> 'a stream \<Rightarrow> bool"
where [code del]: "equal_stream xs ys \<longleftrightarrow> xs = ys"
instance proof qed(simp add: equal_stream_def)
end

lemma equal_stream_code [code]:
  "equal_class.equal (SCons x xs) (SCons y ys) \<longleftrightarrow> (if x = y then equal_class.equal xs ys else False)"
by(simp_all add: equal_stream_def)

declare stream.sets[code] 
(* declare llist_map_simps[code] *)

lemma stream_corec_code [code]:
  "stream_corec SHD endORmore STL_end STL_more b = SCons (SHD b) 
     (if endORmore b then STL_end b
      else stream_corec SHD endORmore STL_end STL_more (STL_more b))"
by(rule stream.expand) simp_all

lemma stream_unfold_code [code]:
  "stream_unfold SHD STL b = SCons (SHD b) (stream_unfold SHD STL (STL b))"
by(rule stream.expand) simp_all

declare stream.sels [code]

text {* Coinduction rules *}

lemmas stream_coinduct [consumes 1, case_names Eqstream] = stream.coinduct
lemmas stream_strong_coinduct [consumes 1, case_names Eqstream] = stream.strong_coinduct

lemma stream_fun_coinduct_invar [consumes 1, case_names SCons]:
  assumes "P x"
  and "\<And>x. P x
  \<Longrightarrow> shd (f x) = shd (g x) \<and>
     ((\<exists>x'. stl (f x) = f x' \<and> stl (g x) = g x' \<and> P x') \<or> stl (f x) = stl (g x))"
  shows "f x = g x"
apply(rule stream.strong_coinduct[of "\<lambda>xs ys. \<exists>x. P x \<and> xs = f x \<and> ys = g x"])
using assms by auto

theorem stream_fun_coinduct [case_names SCons]:
  assumes 
  "\<And>x. shd (f x) = shd (g x) \<and>
      ((\<exists>x'. stl (f x) = f x' \<and> stl (g x) = g x') \<or> stl (f x) = stl (g x))"
  shows "f x = g x"
by(rule stream_fun_coinduct_invar[where P="\<lambda>_. True" and f=f and g=g])(simp_all add: assms)

lemmas stream_fun_coinduct2 = stream_fun_coinduct[where ?'a="'a \<times> 'b", split_format (complete)]
lemmas stream_fun_coinduct3 = stream_fun_coinduct[where ?'a="'a \<times> 'b \<times> 'c", split_format (complete)]
lemmas stream_fun_coinduct4 = stream_fun_coinduct[where ?'a="'a \<times> 'b \<times> 'c \<times> 'd", split_format (complete)]
lemmas stream_fun_coinduct_invar2 = stream_fun_coinduct_invar[where ?'a="'a \<times> 'b", split_format (complete)]
lemmas stream_fun_coinduct_invar3 = stream_fun_coinduct_invar[where ?'a="'a \<times> 'b \<times> 'c", split_format (complete)]
lemmas stream_fun_coinduct_invar4 = stream_fun_coinduct_invar[where ?'a="'a \<times> 'b \<times> 'c \<times> 'd", split_format (complete)]

text {* lemmas about for generated constants *}

lemma eq_SConsD: "xs = SCons y ys \<Longrightarrow> shd xs = y \<and> stl xs = ys"
by auto

lemma stream_map_simps [simp, code]:
  shows smap_SCons: "stream_map f (SCons x xs) = SCons (f x) (stream_map f xs)"
unfolding stream_map_def SCons_def
by(subst stream.ctor_dtor_unfold, simp add: stream.dtor_ctor)

lemma [simp]:
  shows shd_smap: "shd (stream_map f xs) = f (shd xs)"
  and stl_smap: "stl (stream_map f xs) = stream_map f (stl xs)"
by(cases xs, simp_all)+

lemma smap_ident [simp]: "stream_map (\<lambda>x. x) xs = xs"
by(simp only: id_def[symmetric] stream.map_id')

lemma smap_eq_SCons_conv:
  "stream_map f xs = SCons y ys \<longleftrightarrow> 
  (\<exists>x xs'. xs = SCons x xs' \<and> y = f x \<and> ys = stream_map f xs')"
by(cases xs)(auto)

lemma smap_id: 
  "stream_map id = id"
by(simp add: fun_eq_iff stream.map_id')

lemma stream_map_stream_unfold:
  "stream_map f (stream_unfold SHD STL b) = stream_unfold (f \<circ> SHD) STL b"
by(coinduct b rule: stream_fun_coinduct) auto

lemma stream_map_stream_corec:
  "stream_map f (stream_corec SHD endORmore STL_end STL_more b) =
   stream_corec (f \<circ> SHD) endORmore (stream_map f \<circ> STL_end) STL_more b"
by(coinduct b rule: stream_fun_coinduct) auto

lemma stream_unfold_ltl_unroll:
  "stream_unfold SHD STL (STL b) = stream_unfold (SHD \<circ> STL) STL b"
by(coinduct b rule: stream_fun_coinduct) auto

lemma stream_unfold_eq_SCons [simp]:
  "stream_unfold SHD STL b = SCons x xs \<longleftrightarrow>
  x = SHD b \<and> xs = stream_unfold SHD STL (STL b)"
by(subst stream_unfold_code) auto

lemma stream_unfold_id [simp]: "stream_unfold shd stl xs = xs"
by(coinduct xs rule: stream_fun_coinduct) simp_all

lemma sset_neq_empty [simp]: "stream_set xs \<noteq> {}"
by(cases xs) simp_all

lemma shd_in_sset [simp]: "shd xs \<in> stream_set xs"
by(cases xs) auto

lemma sset_stl: "stream_set (stl xs) \<subseteq> stream_set xs"
by(cases xs) auto

lemma in_sset_stlD: "x \<in> stream_set (stl xs) \<Longrightarrow> x \<in> stream_set xs"
using sset_stl[of xs] by auto

text {* induction rules *}

theorem stream_set_induct[consumes 1, case_names find step, induct set: "stream_set"]:
  assumes y: "y \<in> stream_set s" and "\<And>s. P (shd s) s"
  and "\<And>s y. \<lbrakk>y \<in> stream_set (stl s); P y (stl s)\<rbrakk> \<Longrightarrow> P y s"
  shows "P y s"
proof -
  have "\<forall>y \<in> stream_set s. P y s"
    apply (rule stream.dtor_set_induct)
    using assms by(auto simp add:  shd_def stl_def stream_case_def fsts_def snds_def split_beta)
  thus ?thesis using y by blast
qed

text {* Nitpick setup *}

setup {*
  Nitpick.register_codatatype @{typ "'a llist"} @{const_name llist_case}
    (map dest_Const [@{term LNil}, @{term LCons}])
*}

declare
  llist_map_simps [nitpick_simp]
  llist.sels [nitpick_simp]






subsection {* Link to @{typ "'a llist"} *}

definition llist_of_stream :: "'a stream \<Rightarrow> 'a llist"
where "llist_of_stream = llist_unfold (\<lambda>_. False) shd stl"

definition stream_of_llist :: "'a llist \<Rightarrow> 'a stream"
where "stream_of_llist = stream_unfold lhd ltl"

lemma llist_of_stream_neq_LNil [simp]: "llist_of_stream xs \<noteq> LNil"
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
by(coinduct xs rule: stream_fun_coinduct) simp_all

lemma llist_of_stream_stream_of_llist [simp]: 
  assumes "\<not> lfinite xs"
  shows "llist_of_stream (stream_of_llist xs) = xs"
using assms
by(coinduct xs rule: llist_fun_coinduct_invar) auto

lemma lfinite_llist_of_stream [simp]: "\<not> lfinite (llist_of_stream xs)"
proof
  assume "lfinite (llist_of_stream xs)"
  thus False
    by(induct "llist_of_stream xs" arbitrary: xs rule: lfinite_induct) auto
qed

lemma stream_from_llist: "type_definition llist_of_stream stream_of_llist {xs. \<not> lfinite xs}"
by(unfold_locales) simp_all

interpretation stream!: type_definition llist_of_stream stream_of_llist "{xs. \<not> lfinite xs}"
by(rule stream_from_llist)

setup_lifting (no_code) stream_from_llist

lemma cr_streamI: "\<not> lfinite xs \<Longrightarrow> cr_stream xs (stream_of_llist xs)"
by(simp add: cr_stream_def Abs_stream_inverse)

lemma llist_of_stream_stream_unfold [simp]: 
  "llist_of_stream (stream_unfold SHD STL x) = llist_unfold (\<lambda>_. False) SHD STL x"
by(coinduct x rule: llist_fun_coinduct) auto

lemma llist_of_stream_stream_corec [simp]:
  "llist_of_stream (stream_corec SHD endORmore STL_more STL_end x) =
   llist_corec (\<lambda>_. False) SHD endORmore (llist_of_stream \<circ> STL_more) STL_end x"
by(coinduct x rule: llist_fun_coinduct) auto

lemma stream_unfold_transfer [transfer_rule]:
  assumes "is_equality AtoB" "is_equality AtoA" "is_equality A"
  shows
  "(AtoB ===> AtoA ===> A ===> pcr_stream op =) (llist_unfold (\<lambda>_. False)) stream_unfold"
using assms unfolding is_equality_def stream.pcr_cr_eq
by(auto simp add: cr_stream_def intro!: fun_relI)

lemma stream_corec_transfer [transfer_rule]:
  assumes "is_equality AtoB" "is_equality Abool" "is_equality A" "is_equality AtoA"
  shows
  "(AtoB ===> Abool ===> (A ===> pcr_stream op =) ===> AtoA ===> A ===> cr_stream)
   (llist_corec (\<lambda>_. False)) stream_corec"
using assms unfolding is_equality_def stream.pcr_cr_eq
apply(auto intro!: fun_relI simp add: cr_stream_def)
apply(rule fun_cong) back
apply(rule_tac x=yc in fun_cong)
apply(rule_tac x=xb in arg_cong)
apply(auto elim: fun_relE)
done

lemma shd_transfer [transfer_rule]: "(pcr_stream op = ===> op =) lhd shd"
by(auto simp add: cr_stream_def stream.pcr_cr_eq)

lemma stl_transfer [transfer_rule]: "(pcr_stream op = ===> pcr_stream op =) ltl stl"
by(auto simp add: cr_stream_def stream.pcr_cr_eq)

lemma llist_of_stream_SCons [simp]: "llist_of_stream (SCons x xs) = LCons x (llist_of_stream xs)"
by(simp add: llist_of_stream_def)

lemma SCons_transfer [transfer_rule]:
  "is_equality A \<Longrightarrow> (A ===> pcr_stream op = ===> pcr_stream op =) LCons SCons"
by(auto simp add: is_equality_def cr_stream_def stream.pcr_cr_eq intro!: fun_relI)

abbreviation sset where "sset \<equiv> stream_set"

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
    case find
    thus ?case by(transfer)(auto intro: lhd_in_lset)
  next
    case step 
    thus ?case
      by(auto simp add: ltl_llist_of_stream[symmetric] simp del: ltl_llist_of_stream dest: in_lset_ltlD)
  qed
qed

lemma sset_transfer [transfer_rule]: "(pcr_stream op = ===> op =) lset sset"
by(auto simp add: cr_stream_def stream.pcr_cr_eq intro!: fun_relI del: equalityI)

abbreviation smap where "smap \<equiv> stream_map"

lemma llist_of_stream_smap [simp]:
  "llist_of_stream (smap f xs) = lmap f (llist_of_stream xs)"
by(coinduct xs rule: llist_fun_coinduct) auto

lemma smap_transfer [transfer_rule]:
  "is_equality A \<Longrightarrow> (A ===> pcr_stream op = ===> pcr_stream op =) lmap smap"
by(auto simp add: is_equality_def cr_stream_def stream.pcr_cr_eq intro!: fun_relI)

subsection {* Definition of derived operations *}

lift_definition Stream :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a stream" is "inf_llist" by simp

lift_definition snth :: "'a stream \<Rightarrow> nat \<Rightarrow> 'a" is "lnth" ..

lift_definition sconst :: "'a \<Rightarrow> 'a stream" is "iterates id" by simp

lift_definition iterates :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a stream" is "Coinductive_List.iterates" by simp

lift_definition sappend :: "'a list \<Rightarrow> 'a stream \<Rightarrow> 'a stream" is "lappend \<circ> llist_of" by simp

lift_definition szip :: "'a stream \<Rightarrow> 'b stream \<Rightarrow> ('a \<times> 'b) stream" is lzip by simp

lift_definition stream_all2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> 'b stream \<Rightarrow> bool"
is llist_all2 ..

subsection {* Converting between streams and functions: @{term Stream} and @{term snth} *}

lemma Stream_rec [code]: "Stream f = SCons (f 0) (Stream (f \<circ> Suc))"
by transfer (subst inf_llist_rec, simp add: o_def)

lemma snth_Stream [simp]: "snth (Stream f) = f"
by transfer (simp add: fun_eq_iff)

lemma snth_SCons: "snth (SCons x xs) n = (case n of 0 \<Rightarrow> x | Suc n' \<Rightarrow> snth xs n')"
by transfer (simp add: lnth_LCons)

lemma snth_simps [simp, code, nitpick_simp]:
  shows snth_SCons_0: "snth (SCons x xs) 0 = x"
  and snth_SCons_Suc: "snth (SCons x xs) (Suc n) = snth xs n"
by(simp_all add: snth_SCons)

lemma Stream_snth [simp]: "Stream (snth xs) = xs"
by transfer simp

lemma shd_Stream [simp]: "shd (Stream f) = f 0"
by transfer simp

lemma stl_Stream [simp]: "stl (Stream f) = Stream (\<lambda>n. f (Suc n))"
by transfer simp

lemma sset_Stream [simp]: "sset (Stream f) = range f"
by transfer simp

lemma smap_Stream [simp]: "smap f (Stream g) = Stream (f \<circ> g)"
by transfer simp

subsubsection {* The constant stream @{term sconst} *}

lemma sconst: "sconst a = SCons a (sconst a)"
by transfer (subst iterates, simp)

lemma snth_sconst [simp]: "snth (sconst a) n = a"
by transfer (simp add: id_power)

lemma shd_sconst [simp]: "shd (sconst a) = a"
by transfer simp

lemma stl_sconst [simp]: "stl (sconst a) = sconst a"
by transfer simp

lemma sconst_conv_Stream: "sconst a = Stream (\<lambda>_. a)" (is "?lhs = ?rhs")
by(coinduct a rule: stream_fun_coinduct) auto

lemma sset_sconst [simp]: "sset (sconst a) = {a}"
by transfer (simp add: lset_iterates id_power)

subsection{* Function iteration @{term iterates} *}

lemma iterates [nitpick_simp]: "iterates f x = SCons x (iterates f (f x))"
by transfer (rule iterates)

lemma smap_iterates: "smap f (iterates f x) = iterates f (f x)"
by transfer (rule lmap_iterates)

lemma iterates_smap: "iterates f x = SCons x (smap f (iterates f x))"
by transfer (rule iterates_lmap)

lemma snth_iteretes [simp]: "snth (iterates f a) n = (f ^^ n) a"
by transfer simp

lemma shd_iterates [simp]: "shd (iterates f a) = a"
by transfer simp

lemma stl_iterates [simp]: "stl (iterates f a) = iterates f (f a)"
by transfer simp

lemma iterates_conv_Stream: "iterates f a = Stream (\<lambda>n. (f ^^ n) a)"
by transfer (rule iterates_conv_inf_llist)

lemma sset_iterates: "sset (iterates f a) = {(f ^^ n) a|n. True}"
by transfer (rule lset_iterates)

subsection {* Map for streams: @{term smap} *}

lemma snth_smap [simp]: "snth (smap f xs) n = f (snth xs n)"
by transfer (auto dest: not_lfinite_llength intro: lnth_lmap)

lemma smap_sconst [simp]: "smap f (sconst a) = sconst (f a)"
by(coinduct a rule: stream_fun_coinduct) auto

subsection {* Prefixing a stream: @{term sappend} *}

lemma shd_sappend: "shd (sappend xs ys) = (if xs = [] then shd ys else hd xs)"
by transfer simp

lemma stl_sappend: "stl (sappend xs ys) = (if xs = [] then stl ys else sappend (tl xs) ys)"
by transfer (clarsimp simp add: neq_Nil_conv)

lemma sappend_simps [simp, code, nitpick_simp]:
  "sappend [] ys = ys"
  "sappend (x # xs) ys = SCons x (sappend xs ys)"
by(transfer, simp)+

lemma snth_sappend:
  "snth (sappend xs ys) n = (if n < length xs then xs ! n else snth ys (n - length xs))"
by transfer (simp add: lnth_lappend)

lemma sappend_assoc: "sappend (xs @ ys) zs = sappend xs (sappend ys zs)"
by transfer(simp add: lappend_llist_of_llist_of[symmetric] lappend_assoc del: lappend_llist_of_llist_of)

lemma smap_sappend: "smap f (sappend xs ys) = sappend (map f xs) (smap f ys)"
by transfer (simp add: lmap_lappend_distrib)

lemma sset_sappend [simp]: "sset (sappend xs ys) = set xs \<union> sset ys"
by transfer simp

subsection {* Zipping two streams: @{term szip} *}

lemma szip_SCons [simp, code, nitpick_simp]: 
  "szip (SCons x xs) (SCons y ys) = SCons (x, y) (szip xs ys)"
by transfer simp

lemma shd_szip [simp]: "shd (szip xs ys) = (shd xs, shd ys)"
by transfer (auto intro: lhd_lzip)

lemma stl_szip [simp]: "stl (szip xs ys) = szip (stl xs) (stl ys)"
by transfer simp

lemma szip_sconst1 [simp]: "szip (sconst a) xs = smap (Pair a) xs"
by(coinduct xs rule: stream_fun_coinduct) auto

lemma szip_sconst2 [simp]: "szip xs (sconst b) = smap (\<lambda>x. (x, b)) xs"
by(coinduct xs rule: stream_fun_coinduct) auto

lemma snth_szip [simp]: "snth (szip xs ys) n = (snth xs n, snth ys n)"
by transfer (auto simp add: lnth_lzip dest!: not_lfinite_llength)

lemma szip_sappend: 
  "length xs = length us
  \<Longrightarrow> szip (sappend xs ys) (sappend us zs) = sappend (zip xs us) (szip ys zs)"
by(induct xs arbitrary: us)(auto simp add: Suc_length_conv)

lemma szip_iterates:
  "szip (iterates f a) (iterates g b) = iterates (map_pair f g) (a, b)"
by transfer (simp add: lzip_iterates map_pair_def)

lemma szip_smap1: "szip (smap f xs) ys = smap (\<lambda>(x, y). (f x, y)) (szip xs ys)"
by transfer (simp add: lzip_lmap1)

lemma szip_smap2: "szip xs (smap g ys) = smap (\<lambda>(x, y). (x, g y)) (szip xs ys)"
by transfer (simp add: lzip_lmap2)

lemma szip_smap [simp]: "szip (smap f xs) (smap g ys) = smap (\<lambda>(x, y). (f x, g y)) (szip xs ys)"
by transfer (rule lzip_lmap)

lemma smap_fst_szip [simp]: "smap fst (szip xs ys) = xs"
by transfer (simp add: lmap_fst_lzip_conv_ltake not_lfinite_llength ltake_all)

lemma smap_snd_szip [simp]: "smap snd (szip xs ys) = ys"
by transfer (simp add: lmap_snd_lzip_conv_ltake not_lfinite_llength ltake_all)

subsection {* @{term stream_all2} *}

lemma stream_all2_SCons [simp, code, nitpick_simp]:
  "stream_all2 P (SCons x xs) (SCons y ys) \<longleftrightarrow> P x y \<and> stream_all2 P xs ys"
by transfer simp

lemma stream_all2_coinduct:
  assumes "X xs ys"
  and "\<And>xs ys. X xs ys \<Longrightarrow> P (shd xs) (shd ys) \<and> (X (stl xs) (stl ys) \<or> stream_all2 P (stl xs) (stl ys))"
  shows "stream_all2 P xs ys"
using assms
apply transfer
apply(rule_tac X="\<lambda>xs ys. \<not> lfinite xs \<and> \<not> lfinite ys \<and> X xs ys" in llist_all2_coinduct)
apply auto
done

end
