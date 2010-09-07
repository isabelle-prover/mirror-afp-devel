(*  Title:       Prefix ordering on coinductive lists as ordering for type class order
    Author:      Andreas Lochbihler
    Maintainer:  Andreas Lochbihler
*)
theory Coinductive_List_Prefix imports
  Coinductive_List_Lib
  List_Prefix
begin

section {* Prefix ordering on lazy lists as ordering for the type class order *}

subsection {* Instantiation of the order type class *}

instantiation llist :: (type) order begin

definition [code_unfold]: "xs \<le> ys = lprefix xs ys"

definition [code_unfold]: "xs < ys = lstrict_prefix xs ys"

instance
proof(intro_classes)
  fix xs ys zs :: "'a llist"
  show "(xs < ys) = (xs \<le> ys \<and> \<not> ys \<le> xs)"
    unfolding less_llist_def less_eq_llist_def lstrict_prefix_def
    by(auto simp: lprefix_antisym)
  show "xs \<le> xs" unfolding less_eq_llist_def by(rule lprefix_refl)
  show "\<lbrakk>xs \<le> ys; ys \<le> zs\<rbrakk> \<Longrightarrow> xs \<le> zs"
    unfolding less_eq_llist_def by(rule lprefix_trans)
  show "\<lbrakk>xs \<le> ys; ys \<le> xs\<rbrakk> \<Longrightarrow> xs = ys"
    unfolding less_eq_llist_def by(rule lprefix_antisym)
qed

end

lemma le_llist_conv_lprefix [iff]: "op \<le> = lprefix"
by(simp add: less_eq_llist_def ext_iff)

lemma less_llist_conv_lstrict_prefix [iff]: "op < = lstrict_prefix"
by(simp add: less_llist_def ext_iff)

instantiation llist :: (type) bot begin

definition "bot = LNil"

instance
by(intro_classes)(simp add: bot_llist_def)

end

lemma llist_of_lprefix_llist_of [simp]:
  "lprefix (llist_of xs) (llist_of ys) \<longleftrightarrow> xs \<le> ys"
proof(induct xs arbitrary: ys)
  case (Cons x xs) thus ?case
    by(cases ys)(auto simp add: LCons_lprefix_conv)
qed simp

subsection {* Prefix ordering as a lower semilattice *}

instantiation llist :: (type) semilattice_inf begin

definition [code del]:
  "inf xs ys =
   llist_corec (xs, ys)
     (\<lambda>(xs, ys). case xs of LNil \<Rightarrow> None
                   | LCons x xs' \<Rightarrow> 
                      (case ys of LNil \<Rightarrow> None
                         | LCons y ys' \<Rightarrow> if (x = y) then Some (x, xs', ys') else None))"

lemma llist_inf_simps [simp, code, nitpick_simp]:
  "inf LNil xs = LNil"
  "inf xs LNil = LNil"
  "inf (LCons x xs) (LCons y ys) = (if x = y then LCons x (inf xs ys) else LNil)"
unfolding inf_llist_def
by(simp_all add: llist_corec split: llist_split)

instance
proof
  fix xs ys zs :: "'a llist"
  have "(inf xs ys, xs) \<in> {(inf xs ys, xs)|xs ys. True}" by blast
  thus "inf xs ys \<le> xs" unfolding le_llist_conv_lprefix
  proof(coinduct rule: lprefixI)
    case (lprefix zs xs)
    then obtain ys where zs: "zs = inf xs ys" by auto
    show ?case
    proof(cases "\<exists>x xs' ys'. xs = LCons x xs' \<and> ys = LCons x ys'")
      case True
      with zs have ?LeLCons by auto
      thus ?thesis ..
    next
      case False
      with zs have ?LeLNil by(cases xs)(auto, cases ys, auto)
      thus ?thesis ..
    qed
  qed

  have "(inf xs ys, ys) \<in> {(inf xs ys, ys)|xs ys. True}" by blast
  thus "inf xs ys \<le> ys" unfolding le_llist_conv_lprefix
  proof(coinduct rule: lprefixI)
    case (lprefix zs ys)
    then obtain xs where zs: "zs = inf xs ys" by auto
    show ?case
    proof(cases "\<exists>x xs' ys'. xs = LCons x xs' \<and> ys = LCons x ys'")
      case True
      with zs have ?LeLCons by auto
      thus ?thesis ..
    next
      case False
      with zs have ?LeLNil by(cases xs)(auto, cases ys, auto)
      thus ?thesis ..
    qed
  qed

  assume "xs \<le> ys" "xs \<le> zs"
  hence "(xs, inf ys zs) \<in> {(xs, inf ys zs)|xs ys zs. xs \<le> ys \<and> xs \<le> zs}" 
    by blast
  thus "xs \<le> inf ys zs" unfolding le_llist_conv_lprefix
  proof(coinduct rule: lprefixI)
    case (lprefix xs us)
    then obtain ys zs where us: "us = inf ys zs" 
      and le: "xs \<le> ys" "xs \<le> zs" unfolding le_llist_conv_lprefix by blast
    show ?case
    proof(cases xs)
      case LNil
      thus ?thesis ..
    next
      case (LCons x xs')
      with le obtain ys' zs' where "ys = LCons x ys'" "zs = LCons x zs'"
	"xs' \<le> ys'" "xs' \<le> zs'" by(auto simp add: LCons_lprefix_conv)
      with us LCons have ?LeLCons by auto
      thus ?thesis ..
    qed
  qed
qed

end

end
