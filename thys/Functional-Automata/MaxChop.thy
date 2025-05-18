(*  Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

section "Generic scanner"

theory MaxChop
imports MaxPrefix 
begin

type_synonym 'a chopper = "'a list \<Rightarrow> 'a list list * 'a list"

definition
 is_maxchopper :: "('a list \<Rightarrow> bool) \<Rightarrow> 'a chopper \<Rightarrow> bool" where
"is_maxchopper P chopper =
 (\<forall>xs zs yss.
    (chopper(xs) = (yss,zs)) =
    (xs = concat yss @ zs \<and> (\<forall>ys \<in> set yss. ys \<noteq> []) \<and>
     (case yss of
        [] \<Rightarrow> is_maxpref P [] xs
      | us#uss \<Rightarrow> is_maxpref P us xs \<and> chopper(concat(uss)@zs) = (uss,zs))))"

definition
 reducing :: "'a splitter \<Rightarrow> bool" where
"reducing splitf =
 (\<forall>xs ys zs. splitf xs = (ys,zs) \<and> ys \<noteq> [] \<longrightarrow> length zs < length xs)"

function chop :: "'a splitter \<Rightarrow> 'a list \<Rightarrow> 'a list list \<times> 'a list" where
  [simp del]: "chop splitf xs = (if reducing splitf
                      then let pp = splitf xs
                           in if fst pp = [] then ([], xs)
                           else let qq = chop splitf (snd pp)
                                in (fst pp # fst qq, snd qq)
                      else undefined)"
by pat_completeness auto

termination  
proof (relation "measure (length \<circ> snd)") 
qed (auto simp: reducing_def fst_def split: prod.splits)

lemma chop_rule: "reducing splitf \<Longrightarrow>
  chop splitf xs = (let (pre, post) = splitf xs
                    in if pre = [] then ([], xs)
                       else let (xss, zs) = chop splitf post
                            in (pre # xss,zs))"
by (metis (no_types, lifting) case_prod_unfold chop.simps)

lemma reducing_maxsplit: "reducing(\<lambda>qs. maxsplit P ([],qs) [] qs)"
by (simp add: reducing_def maxsplit_eq)

lemma is_maxsplitter_reducing:
 "is_maxsplitter P splitf \<Longrightarrow> reducing splitf"
by(simp add:is_maxsplitter_def reducing_def)

lemma chop_concat[rule_format]: 
  "is_maxsplitter P splitf \<Longrightarrow>
  (\<forall>yss. chop splitf xs = (yss,zs) \<longrightarrow> xs = concat yss @ zs)"
proof (induction xs rule: measure_induct_rule [where f=length])
  case (less x)
  then show ?case
    apply (simp (no_asm_simp) split del: if_split
        add: chop_rule[OF is_maxsplitter_reducing])
    apply (simp add: Let_def is_maxsplitter_def split: prod.split)
    done
qed

lemma chop_nonempty: "is_maxsplitter P splitf \<Longrightarrow>
  \<forall>yss zs. chop splitf xs = (yss,zs) \<longrightarrow> (\<forall>ys \<in> set yss. ys \<noteq> [])"
proof (induction xs rule: measure_induct_rule [where f=length])
  case (less xs)
  then show ?case
    apply (simp (no_asm_simp) add: chop_rule is_maxsplitter_reducing)
    apply (simp add: Let_def is_maxsplitter_def split: prod.split)
    by (metis "less.prems" is_maxsplitter_reducing reducing_def)
qed

lemma is_maxchopper_chop:
  assumes "is_maxsplitter P splitf" 
  shows "is_maxchopper P (chop splitf)"
  unfolding is_maxchopper_def
proof (intro iffI conjI strip)
  note assms[simplified is_maxsplitter_def, simp]
  fix xs zs yss
  assume "chop splitf xs = (yss, zs)"
  then show "case yss of [] \<Rightarrow> is_maxpref P [] xs
     | us # uss \<Rightarrow> is_maxpref P us xs \<and> 
        chop splitf (concat uss @ zs) = (uss, zs)"
  using chop_concat [OF assms]
  apply(simp add: assms[THEN is_maxsplitter_reducing[THEN chop_rule]])
   apply (force simp: Let_def split: prod.splits if_split_asm)
  done
next
  fix xs zs yss
  assume "xs = concat yss @ zs \<and> (\<forall>ys\<in>set yss. ys \<noteq> []) 
             \<and> (case yss of [] \<Rightarrow> is_maxpref P [] xs | us # uss \<Rightarrow> is_maxpref P us xs \<and> chop splitf (concat uss @ zs) = (uss, zs))"
  then
  show "chop splitf xs = (yss, zs)"
  using chop_concat [OF assms]
  apply (subst assms[THEN is_maxsplitter_reducing, THEN chop_rule])
  apply (simp add: Let_def is_maxpref_def assms[simplified is_maxsplitter_def]
      split: prod.split list.splits)
  apply blast
  by (metis Pair_inject prefix_order.antisym_conv same_append_eq)
qed (use assms chop_concat chop_nonempty in blast)+

end
