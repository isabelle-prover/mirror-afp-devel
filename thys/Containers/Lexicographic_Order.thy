(*  Title:      Containers/Lexicographic_Order.thy
    Author:     Andreas Lochbihler, KIT *)

theory Lexicographic_Order imports
  List_Fusion
  "~~/src/HOL/Library/Quotient_List"
  "~~/src/HOL/Library/Char_ord"
begin

section {* Lexicographic order as a predicate *}

subsection {* Definition *}

context ord begin

inductive lexord :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  Nil: "lexord [] (y # ys)"
| Cons: "x < y \<Longrightarrow> lexord (x # xs) (y # ys)"
| Cons_eq: "\<lbrakk> \<not> x < y; \<not> y < x; lexord xs ys \<rbrakk> \<Longrightarrow> lexord (x # xs) (y # ys)"

lemma lexord_simps [simp]:
  "lexord [] ys = (ys \<noteq> [])"
  "lexord xs [] = False"
  "lexord (x # xs) (y # ys) \<longleftrightarrow> x < y \<or> \<not> y < x \<and> lexord xs ys"
by(subst lexord.simps, fastforce simp add: neq_Nil_conv)+

inductive lexord_eq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  Nil: "lexord_eq [] ys"
| Cons: "x < y \<Longrightarrow> lexord_eq (x # xs) (y # ys)"
| Cons_eq: "\<lbrakk> \<not> x < y; \<not> y < x; lexord_eq xs ys \<rbrakk> \<Longrightarrow> lexord_eq (x # xs) (y # ys)"

lemma lexord_eq_simps [simp]:
  "lexord_eq [] ys = True"
  "lexord_eq xs [] \<longleftrightarrow> xs = []"
  "lexord_eq (x # xs) [] = False"
  "lexord_eq (x # xs) (y # ys) \<longleftrightarrow> x < y \<or> \<not> y < x \<and> lexord_eq xs ys"
by(subst lexord_eq.simps, fastforce)+

end

declare ord.lexord_simps [simp, code]
declare ord.lexord_eq_simps [code, simp]

lemma lexord_code [code, code_unfold]: "lexord = ord.lexord less"
unfolding lexord_def ord.lexord_def ..

context linorder begin

lemma lexord_cases [consumes 1, case_names Nil Cons Cons_eq, cases pred: lexord]:
  assumes "lexord xs ys"
  obtains (Nil) y ys' where "xs = []" "ys = y # ys'"
  | (Cons) x xs' y ys' where "xs = x # xs'" "ys = y # ys'" "x < y"
  | (Cons_eq) x xs' ys' where "xs = x # xs'" "ys = x # ys'" "lexord xs' ys'"
using assms by cases (fastforce simp add: not_less_iff_gr_or_eq)+

lemma lexord_induct [consumes 1, case_names Nil Cons Cons_eq, induct pred: lexord]:
  assumes major: "lexord xs ys"
  and Nil: "\<And>y ys. P [] (y # ys)"
  and Cons: "\<And>x xs y ys. x < y \<Longrightarrow> P (x # xs) (y # ys)"
  and Cons_eq: "\<And>x xs ys. \<lbrakk> lexord xs ys; P xs ys \<rbrakk> \<Longrightarrow> P (x # xs) (x # ys)"
  shows "P xs ys"
using major by induct (simp_all add: Nil Cons not_less_iff_gr_or_eq Cons_eq)

end

subsection {* Properties *}

context ord begin

lemma lexord_append_rightI: "ys \<noteq> Nil \<Longrightarrow> lexord xs (xs @ ys)"
by(induct xs)(auto simp add: neq_Nil_conv)

lemma lexord_append_left_rightI: "x < y \<Longrightarrow> lexord (us @ x # xs) (us @ y # ys)"
by(induct us) auto

lemma lexord_eq_refl: "lexord_eq xs xs"
by(induct xs) simp_all

lemma lexord_append_leftI: "lexord us vs \<Longrightarrow> lexord (xs @ us) (xs @ vs)"
by(induct xs) auto

lemma lexord_append_leftD: "\<lbrakk> lexord (xs @ us) (xs @ vs); \<forall>a. \<not> a < a \<rbrakk> \<Longrightarrow> lexord us vs"
by(induct xs) auto

lemma lexord_irreflexive: 
  assumes irrefl: "\<forall>x. \<not> x < x"
  shows "\<not> lexord xs xs"
proof
  assume "lexord xs xs"
  thus False by(induct xs ys\<equiv>xs)(simp_all add: irrefl)
qed

lemma lexord_into_lexord_eq:
  assumes "lexord xs ys"
  shows "lexord_eq xs ys"
using assms by induct simp_all

end

context order begin

lemma lexord_antisym:
  assumes "lexord xs ys" "lexord ys xs"
  shows False
using assms by induct auto

lemma lexord_irreflexive': "\<not> lexord xs xs"
by(rule lexord_irreflexive) simp

end

context linorder begin

lemma lexord_iff:
  "lexord xs ys \<longleftrightarrow> (\<exists>x vs. ys = xs @ x # vs) \<or> (\<exists>us a b vs ws. a < b \<and> xs = us @ a # vs \<and> ys = us @ b # ws)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs thus ?rhs
  proof induct
    case Cons_eq thus ?case by simp (metis append.simps(2))
  qed(fastforce intro: disjI2 del: disjCI intro: exI[where x="[]"])+
next
  assume ?rhs thus ?lhs
    by(auto intro: lexord_append_leftI[where us="[]", simplified] lexord_append_leftI)
qed

lemma lexord_take_index_conv:
  "lexord xs ys \<longleftrightarrow> 
   (length xs < length ys \<and> take (length xs) ys = xs) \<or>
   (\<exists>i < min (length xs) (length ys). take i xs = take i ys \<and> xs ! i < ys ! i)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs thus ?rhs
    by induct (auto 4 3 del: disjCI intro: disjI2 exI[where x="Suc i", standard])
next
  assume ?rhs (is "?prefix \<or> ?less") thus ?lhs 
  proof
    assume "?prefix"
    hence "ys = xs @ hd (drop (length xs) ys) # tl (drop (length xs) ys)"
      by (metis append_Nil2 append_take_drop_id hd.simps less_not_refl list.exhaust tl.simps(2))
    thus ?thesis unfolding lexord_iff by blast
  next
    assume "?less"
    then obtain i where "i < min (length xs) (length ys)"
      and "take i xs = take i ys" and nth: "xs ! i < ys ! i" by blast
    hence "xs = take i xs @ xs ! i # drop (Suc i) xs" "ys = take i xs @ ys ! i # drop (Suc i) ys"
      by -(subst append_take_drop_id[symmetric, of _ i], simp_all add: drop_Suc_conv_tl)
    with nth show ?thesis unfolding lexord_iff by blast
  qed
qed

-- {* lexord is extension of partial ordering List.lex *} 
lemma lexord_lex: "(xs, ys) \<in> lex {(xs, ys). xs < ys} \<longleftrightarrow> lexord xs ys \<and> length xs = length ys"
proof(induct xs arbitrary: ys)
  case Nil thus ?case by clarsimp
next
  case Cons thus ?case by(cases ys)(simp_all, safe, simp)
qed

lemma lexord_eq_antisym: 
  assumes "lexord_eq xs ys" "lexord_eq ys xs" 
  shows "xs = ys"
using assms by induct simp_all

lemma lexord_eq_trans:
  assumes "lexord_eq xs ys" and "lexord_eq ys zs"
  shows "lexord_eq xs zs"
using assms
apply(induct arbitrary: zs)
apply(case_tac [2-3] zs)
apply auto
done

lemma lexord_trans:
  assumes "lexord xs ys" "lexord ys zs"
  shows "lexord xs zs"
using assms
apply(induct arbitrary: zs)
apply(case_tac [2-3] zs)
apply auto
done

lemma lexord_linear: "lexord xs ys \<or> xs = ys \<or> lexord ys xs"
proof(induct xs arbitrary: ys)
  case Nil thus ?case by(cases ys) simp_all
next
  case Cons thus ?case by(cases ys) auto
qed

lemma lexord_conv_lexord_eq: "lexord xs ys \<longleftrightarrow> lexord_eq xs ys \<and> \<not> lexord_eq ys xs"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  moreover hence "\<not> lexord_eq ys xs" by induct simp_all
  ultimately show ?rhs by(simp add: lexord_into_lexord_eq)
next
  assume ?rhs
  hence "lexord_eq xs ys" "\<not> lexord_eq ys xs" by simp_all
  thus ?lhs by induct simp_all
qed

lemma lexord_eq_linear: "lexord_eq xs ys \<or> lexord_eq ys xs"
apply(induct xs arbitrary: ys)
apply(case_tac [!] ys)
apply auto
done

lemma lexord_linorder: "class.linorder lexord_eq lexord"
by unfold_locales(auto simp add: lexord_conv_lexord_eq lexord_eq_refl lexord_eq_antisym intro: lexord_eq_trans del: disjCI intro: lexord_eq_linear)

lemma lexord_eq_conv_lexord: "lexord_eq xs ys \<longleftrightarrow> xs = ys \<or> lexord xs ys"
by(auto simp add: lexord_conv_lexord_eq lexord_eq_refl dest: lexord_eq_antisym)

end

subsection {* Setup for list fusion *}

context ord begin

definition lexord_fusion :: "('a, 's1) generator \<Rightarrow> ('a, 's2) generator \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool"
where [code del]: "lexord_fusion g1 g2 s1 s2 = lexord (list.unfoldr g1 s1) (list.unfoldr g2 s2)"

definition lexord_eq_fusion :: "('a, 's1) generator \<Rightarrow> ('a, 's2) generator \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool"
where [code del]: "lexord_eq_fusion g1 g2 s1 s2 = lexord_eq (list.unfoldr g1 s1) (list.unfoldr g2 s2)"

lemma lexord_fusion_code:
  "lexord_fusion g1 g2 s1 s2 \<longleftrightarrow>
  (if list.has_next g1 s1 then
     if list.has_next g2 s2 then
       let (x, s1') = list.next g1 s1;
           (y, s2') = list.next g2 s2
       in x < y \<or> \<not> y < x \<and> lexord_fusion g1 g2 s1' s2'
     else False
   else list.has_next g2 s2)"
unfolding lexord_fusion_def
by(subst (1 2) list.unfoldr.simps)(auto split: prod.split_asm)

lemma lexord_eq_fusion_code:
  "lexord_eq_fusion g1 g2 s1 s2 \<longleftrightarrow>
  (list.has_next g1 s1 \<longrightarrow>
   list.has_next g2 s2 \<and>
   (let (x, s1') = list.next g1 s1;
        (y, s2') = list.next g2 s2
    in x < y \<or> \<not> y < x \<and> lexord_eq_fusion g1 g2 s1' s2'))"
unfolding lexord_eq_fusion_def
by(subst (1 2) list.unfoldr.simps)(auto split: prod.split_asm)

end

lemmas [code] =
  lexord_fusion_code ord.lexord_fusion_code
  lexord_eq_fusion_code ord.lexord_eq_fusion_code

lemmas [symmetric, code_unfold] =
  lexord_fusion_def ord.lexord_fusion_def
  lexord_eq_fusion_def ord.lexord_eq_fusion_def

subsection {* Lexicographic order on @{typ String.literal} *}

setup_lifting (no_code) type_definition_literal

instantiation String.literal :: linorder begin
lift_definition less_literal :: "String.literal \<Rightarrow> String.literal \<Rightarrow> bool" is "ord.lexord op <" .
lift_definition less_eq_literal :: "String.literal \<Rightarrow> String.literal \<Rightarrow> bool" is "ord.lexord_eq op <" .

instance
proof -
  interpret linorder "ord.lexord_eq op <" "ord.lexord op < :: string \<Rightarrow> string \<Rightarrow> bool"
    by(rule linorder.lexord_linorder[where less_eq="op \<le>"])(unfold_locales)
  show "PROP ?thesis"
    by(intro_classes)(transfer, (simp add: less_le_not_le linear))+
qed
end

lemma less_literal_code [code]: 
  "op < = (\<lambda>xs ys. ord.lexord op < (explode xs) (explode ys))"
by(simp add: less_literal.rep_eq fun_eq_iff)

lemma less_eq_literal_code [code]:
  "op \<le> = (\<lambda>xs ys. ord.lexord_eq op < (explode xs) (explode ys))"
by(simp add: less_eq_literal.rep_eq fun_eq_iff)

end
