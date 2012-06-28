(*  Title:      HOL/Library/Coinductive_Stream.thy
    Author:     Peter Gammie and Andreas Lochbihler
*)
header {* Coinductive streams *}

theory Coinductive_Stream
imports
  Coinductive_List_Lib
  "~~/src/HOL/Library/Quotient_Product"
  "~~/src/HOL/Library/Quotient_Set"
begin

definition "is_equality R \<longleftrightarrow> (R = (op =))" (* TODO: move to Transfer.thy *)

lemma is_equality_intros [transfer_rule]:
  "is_equality (op =)"
  "is_equality A \<Longrightarrow> is_equality B \<Longrightarrow> is_equality (fun_rel A B)"
  "is_equality A \<Longrightarrow> is_equality B \<Longrightarrow> is_equality (prod_rel A B)"
  "is_equality A \<Longrightarrow> is_equality (set_rel A)"
  unfolding is_equality_def
  by (simp_all add: fun_rel_eq prod_rel_eq set_rel_eq)

lemma id_power: "id ^^ n = id"
by(induct n) auto

subsection {* Type definition *}

typedef (open) 'a stream = "{xs :: 'a llist. \<not> lfinite xs}"
proof
  show "iterates undefined undefined \<in> ?stream" by simp
qed

setup_lifting (no_code) type_definition_stream

lemma cr_streamI: "\<not> lfinite xs \<Longrightarrow> cr_stream xs (Abs_stream xs)"
by(simp add: cr_stream_def Abs_stream_inverse)

lift_definition SCons :: "'a \<Rightarrow> 'a stream \<Rightarrow> 'a stream" is LCons by simp

code_datatype SCons

lemma SCons_inject [iff, induct_simp]: "(SCons x xs = SCons y ys) = (x = y \<and> xs = ys)"
by transfer simp

declare SCons.transfer [transfer_rule del]

(* FIXME: generate rules in this new format automatically *)
lemma SCons_transfer' [transfer_rule]:
  "is_equality A \<Longrightarrow> (A ===> cr_stream ===> cr_stream) LCons SCons"
  unfolding is_equality_def by (simp add: SCons.transfer)

lemma stream_cases [cases type: stream]:
  obtains (SCons) x l' where "l = SCons x l'"
proof(transfer fixing: thesis)
  fix l
  assume "\<not> lfinite l" and "\<And>x l'. \<lbrakk>\<not> lfinite l'; l = LCons x l'\<rbrakk> \<Longrightarrow> thesis"
  thus thesis by(cases l) simp_all
qed

lift_definition stream_case :: "('a \<Rightarrow> 'a stream \<Rightarrow> 'b) \<Rightarrow> 'a stream \<Rightarrow> 'b" 
  is "llist_case undefined"
by(auto split: llist_split)

translations
  "case p of XCONST SCons x l \<Rightarrow> b" \<rightleftharpoons> "CONST stream_case (\<lambda>x l. b) p"
  "case p of (XCONST SCons :: 'b) x l \<Rightarrow> b" \<rightharpoonup> "CONST stream_case (\<lambda>x l. b) p"

lemma stream_case_SCons [simp, code]: "stream_case d (SCons M N) = d M N"
by transfer simp

lemma stream_case_cert:
  assumes "CASE \<equiv> stream_case d"
  shows "CASE (SCons M N) \<equiv> d M N"
using assms by simp

setup {* Code.add_case @{thm stream_case_cert} *}

setup {*
  Nitpick.register_codatatype @{typ "'a stream"} @{const_name stream_case}
    (map dest_Const [@{term SCons}])
*}

lift_definition stream_corec :: "'a \<Rightarrow> ('a \<Rightarrow> 'b \<times> 'a) \<Rightarrow> 'b stream" is "\<lambda>a f. llist_corec a (Some \<circ> f)"
proof
  fix a :: 'a and f :: "'a \<Rightarrow> 'b \<times> 'a"
  assume "lfinite (llist_corec a (Some \<circ> f))"
  thus False
  proof(induct xs\<equiv>"llist_corec a (Some \<circ> f)" arbitrary: a)
    case lfinite_LNil thus ?case
      by(subst (asm) llist_corec)(simp add: split_beta)
  next
    case lfinite_LConsI thus ?case
      by(subst (asm) (2) llist_corec)(auto simp add: split_beta)
  qed
qed

lemma stream_corec [code, nitpick_simp]:
  "stream_corec a f = (case f a of (z, w) \<Rightarrow> SCons z (stream_corec w f))"
by transfer (subst llist_corec, simp)

lemma stream_equalityI
  [consumes 1, case_names Eqstream, case_conclusion Eqstream EqSCons]:
  assumes "(l1, l2) \<in> r"
    and "\<And>q. q \<in> r \<Longrightarrow>
        (\<exists>l1 l2 a b.
          q = (SCons a l1, SCons b l2) \<and> a = b \<and>
            ((l1, l2) \<in> r \<or> l1 = l2))"
      (is "\<And>q. _ \<Longrightarrow> ?EqSCons q")
  shows "l1 = l2"
using assms
proof transfer
  fix l1 l2 :: "'a llist" and r
  assume l1: "\<not> lfinite l1" and l2: "\<not> lfinite l2"
    and r: "Domainp (set_rel (prod_rel cr_stream cr_stream)) r"
    and in_r: "(l1, l2) \<in> r"
    and step: "\<And>q. \<lbrakk>Domainp (prod_rel cr_stream cr_stream) q; q \<in> r\<rbrakk>
      \<Longrightarrow> \<exists>l1\<in>{xs. \<not> lfinite xs}. \<exists>l2\<in>{xs. \<not> lfinite xs}. 
            \<exists>a b. q = (LCons a l1, LCons b l2) \<and> a = b \<and> ((l1, l2) \<in> r \<or> l1 = l2)"
  have "(l1, l2) \<in> {(l1, l2). \<not> lfinite l1 \<and> \<not> lfinite l2 \<and> (l1, l2) \<in> r}" 
    using l1 l2 in_r by blast
  thus "l1 = l2"
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    hence "Domainp (prod_rel cr_stream cr_stream) q" "q \<in> r"
      by(auto 4 3 simp add: Domainp.simps intro: cr_streamI)
    from step[OF this] show ?case by clarsimp
  qed
qed

lemma stream_fun_equalityI[case_names SCons, case_conclusion SCons EqSCons]:
  assumes fun_SCons: "\<And>x l.
        (\<exists>l1 l2 a b.
          (f (SCons x l), g (SCons x l)) = (SCons a l1, SCons b l2) \<and>
            a = b \<and> ((l1, l2) \<in> {(f u, g u) | u. True} \<or> l1 = l2))"
      (is "\<And>x l. ?fun_SCons x l")
  shows "f l = g l"
proof -
  have "(f l, g l) \<in> {(f l, g l) | l. True}" by blast
  then show ?thesis
  proof (coinduct rule: stream_equalityI)
    case (Eqstream q)
    then obtain l where q: "q = (f l, g l)" by blast
    show ?case
    proof (cases l)
      case (SCons x l')
      with `?fun_SCons x l'` q SCons show ?thesis by blast
    qed
  qed
qed

subsection {* Definition of derived operations *}

lift_definition Stream :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a stream" is "inf_llist" by simp

lift_definition shd :: "'a stream \<Rightarrow> 'a" is lhd ..

lift_definition stl :: "'a stream \<Rightarrow> 'a stream" is ltl by simp

lift_definition snth :: "'a stream \<Rightarrow> nat \<Rightarrow> 'a" is "lnth" ..

lift_definition smap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a stream \<Rightarrow> 'b stream" is lmap by simp

lift_definition sconst :: "'a \<Rightarrow> 'a stream" is "iterates id" by simp

lift_definition iterates :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a stream" is "Coinductive_List.iterates" by simp

lift_definition sappend :: "'a list \<Rightarrow> 'a stream \<Rightarrow> 'a stream" is "lappend \<circ> llist_of" by simp

lift_definition sset :: "'a stream \<Rightarrow> 'a set" is "lset" ..

lift_definition szip :: "'a stream \<Rightarrow> 'b stream \<Rightarrow> ('a \<times> 'b) stream" is lzip by simp

lemmas stream_old_transfers [transfer_rule del] =
  shd.transfer snth.transfer smap.transfer sconst.transfer iterates.transfer

(* FIXME: generate these rules automatically *)
lemma stream_transfers [transfer_rule]:
  "is_equality A \<Longrightarrow> (cr_stream ===> A) lhd shd"
  "is_equality A \<Longrightarrow> (cr_stream ===> op = ===> A) lnth snth"
  "is_equality A \<Longrightarrow> is_equality B \<Longrightarrow> ((A ===> B) ===> cr_stream ===> cr_stream) lmap smap"
  "is_equality A \<Longrightarrow> (A ===> cr_stream) (Coinductive_List.iterates id) sconst"
  "is_equality A \<Longrightarrow> ((A ===> A) ===> A ===> cr_stream)
    Coinductive_List.iterates Coinductive_Stream.iterates"
  by (simp_all add: is_equality_def stream_old_transfers)

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
by(coinduct rule: stream_fun_equalityI)(subst Stream_rec, simp add: o_def)


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
proof -
  def lhs \<equiv> "?lhs" and rhs \<equiv> "?rhs"
  hence "(lhs, rhs) \<in> {(?lhs, ?rhs)}" by simp
  thus "lhs = rhs"
    by(coinduct rule: stream_equalityI)(subst (asm) sconst, subst (asm) Stream_rec, auto simp add: o_def)
qed

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

subsection {* Head and tail of a stream: @{term "shd"} and @{term "stl"} *}

lemma shd_SCons [simp, code, nitpick_simp]: "shd (SCons x xs) = x"
by transfer simp

lemma shd_Stream [simp]: "shd (Stream f) = f 0"
by transfer simp

lemma shd_smap [simp]: "shd (smap f xs) = f (shd xs)"
by transfer (auto intro: lhd_lmap)

lemma shd_sappend: "shd (sappend xs ys) = (if xs = [] then shd ys else hd xs)"
by transfer (clarsimp simp add: neq_Nil_conv)

lemma stl_SCons [simp, code, nitpick_simp]: "stl (SCons x xs) = xs"
by transfer simp

lemma stl_Stream: "stl (Stream f) = Stream (f \<circ> Suc)"
by transfer (simp add: o_def)

lemma stl_smap: "stl (smap f xs) = smap f (stl xs)"
by transfer (simp add: ltl_lmap)

lemma stl_sappend: "stl (sappend xs ys) = (if xs = [] then stl ys else sappend (tl xs) ys)"
by transfer (clarsimp simp add: neq_Nil_conv)

lemma SCons_shd_stl [simp]: "SCons (shd xs) (stl xs) = xs"
by(cases xs) simp

subsection {* Map for streams: @{term smap} *}

lemma smap_LCons [simp, nitpick_simp, code]:
  "smap f (SCons M N) = SCons (f M) (smap f N)"
by transfer simp

lemma smap_compose [simp]: "smap (f o g) l = smap f (smap g l)"
by transfer simp

lemma smap_ident [simp]: "smap (\<lambda>x. x) l = l"
by transfer simp

lemma snth_smap [simp]: "snth (smap f xs) n = f (snth xs n)"
by transfer (auto dest: not_lfinite_llength intro: lnth_lmap)

lemma smap_sconst [simp]: "smap f (sconst a) = sconst (f a)" (is "?lhs = ?rhs")
proof -
  def lhs \<equiv> "?lhs" and rhs \<equiv> "?rhs"
  hence "(lhs, rhs) \<in> {(?lhs, ?rhs)}" by simp
  thus "lhs = rhs"
    by(coinduct rule: stream_equalityI)(subst (asm) (1 2) sconst, simp)
qed

subsection {* Prefixing a stream: @{term sappend} *}

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

subsection {* Elements of a stream: @{term sset} *}

lemma sset_SCons [simp, code]: "sset (SCons x xs) = insert x (sset xs)"
by transfer simp

lemma sset_sappend [simp]: "sset (sappend xs ys) = set xs \<union> sset ys"
by transfer simp

lemma sset_smap [simp]: "sset (smap f xs) = f ` sset xs"
by transfer simp

lemma sset_sconst [simp]: "sset (sconst a) = {a}"
by transfer (simp add: lset_iterates id_power)

lemma sset_iterates: "sset (iterates f a) = {(f ^^ n) a|n. True}"
by transfer (rule lset_iterates)

lemma sset_Stream [simp]: "sset (Stream f) = range f"
by transfer simp

lemma smap_Stream [simp]: "smap f (Stream g) = Stream (f \<circ> g)"
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
by(rule stream_fun_equalityI[where l=xs])(subst sconst, auto)

lemma szip_sconst2 [simp]: "szip xs (sconst b) = smap (\<lambda>x. (x, b)) xs"
by(rule stream_fun_equalityI[where l=xs])(subst sconst, auto)

lemma snth_szip [simp]: "snth (szip xs ys) n = (snth xs n, snth ys n)"
by transfer (auto simp add: lnth_lzip dest!: not_lfinite_llength)

lemma szip_sappend: 
  "length xs = length us
  \<Longrightarrow> szip (sappend xs ys) (sappend us zs) = sappend (zip xs us) (szip ys zs)"
by(induct xs arbitrary: us)(auto simp add: Suc_length_conv)

lemma szip_iterates:
  "szip (iterates f a) (iterates g b) = iterates (\<lambda>(a, b). (f a, g b)) (a, b)"
by transfer (rule lzip_iterates)

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

end
