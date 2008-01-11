(*  ID:         $Id: LinArith.thy,v 1.2 2008-01-11 15:22:16 lsf37 Exp $
    Author:     Tobias Nipkow, 2007
*)

header{* Linear real arithmetic *}

theory LinArith
imports QE ListSpace Complex_Main
begin

subsection{*Basics*}

subsubsection{*Syntax and Semantics*}

datatype atom = Less real "real list" | Eq real "real list"

fun is_Less :: "atom \<Rightarrow> bool" where
"is_Less (Less r rs) = True" |
"is_Less f = False"

abbreviation "is_Eq \<equiv> Not o is_Less"

lemma is_Less_iff: "is_Less f = (\<exists>r rs. f = Less r rs)"
by(induct f) auto

lemma is_Eq_iff: "(\<forall>i j. a \<noteq> Less i j) = (\<exists>i j. a = Eq i j)"
by(cases a) auto

fun neg\<^isub>R :: "atom \<Rightarrow> atom fm" where
"neg\<^isub>R (Less r t) = Or (Atom(Less (-r) (-t))) (Atom(Eq r t))" |
"neg\<^isub>R (Eq r t) = Or (Atom(Less r t)) (Atom(Less (-r) (-t)))"

fun hd_coeff :: "atom \<Rightarrow> real" where
"hd_coeff (Less r cs) = (case cs of [] \<Rightarrow> 0 | c#_ \<Rightarrow> c)" |
"hd_coeff (Eq r cs) = (case cs of [] \<Rightarrow> 0 | c#_ \<Rightarrow> c)"

definition "depends\<^isub>R a = (hd_coeff a \<noteq> 0)"

fun decr\<^isub>R :: "atom \<Rightarrow> atom" where
"decr\<^isub>R (Less r rs) = Less r (tl rs)" |
"decr\<^isub>R (Eq r rs) = Eq r (tl rs)"

fun I\<^isub>R :: "atom \<Rightarrow> real list \<Rightarrow> bool" where
"I\<^isub>R (Less r cs) xs = (r < \<langle>cs,xs\<rangle>)" |
"I\<^isub>R (Eq r cs) xs = (r = \<langle>cs,xs\<rangle>)"

definition "atoms\<^isub>0 = ATOM.atoms\<^isub>0 depends\<^isub>R"
(* FIXME !!! (incl: display should hide params)*)

interpretation R: ATOM [neg\<^isub>R "(\<lambda>a. True)" I\<^isub>R depends\<^isub>R decr\<^isub>R]
  where "ATOM.atoms\<^isub>0 depends\<^isub>R = atoms\<^isub>0"
proof -
  case goal1
  thus ?case
    apply(unfold_locales)
        apply(case_tac a)
         apply simp_all
     apply(case_tac a)
      apply simp_all
      apply arith
     apply arith
    apply(case_tac a)
    apply(simp_all add:depends\<^isub>R_def split:list.splits)
    done
next
  case goal2
  thus ?case by(simp add:atoms\<^isub>0_def)
qed

setup {* Sign.revert_abbrev "" @{const_name R.I} *}
setup {* Sign.revert_abbrev "" @{const_name R.lift_nnf_qe} *}


subsubsection{*Shared constructions*}

fun combine :: "(real * real list) \<Rightarrow> (real * real list) \<Rightarrow> atom" where
"combine (r\<^isub>1,cs\<^isub>1) (r\<^isub>2,cs\<^isub>2) = Less (r\<^isub>1-r\<^isub>2) (cs\<^isub>2 - cs\<^isub>1)"

(* More efficient combination than rhs of combine_conv below; unused
lemma combine_code:
  "combine (r1,c1,cs1) (r2,c2,cs2) =
  Less (c1*r2-c2*r1) (zipwith0 (%x y. c1*y-c2*x) cs1 cs2)"
apply(rule sym)
apply(simp)
apply(induct cs1 arbitrary:cs2)
 apply simp
apply(case_tac cs2)
 apply simp
apply simp
done*)

definition "lbounds as = [(r/c, (-1/c) *\<^sub>s cs). Less r (c#cs) \<leftarrow> as, c>0]"
definition "ubounds as = [(r/c, (-1/c) *\<^sub>s cs). Less r (c#cs) \<leftarrow> as, c<0]"
definition "ebounds as = [(r/c, (-1/c) *\<^sub>s cs). Eq r (c#cs) \<leftarrow> as, c\<noteq>0]"

lemma set_lbounds:
 "set(lbounds as) = {(r/c, (-1/c) *\<^sub>s cs)|r c cs. Less r (c#cs) : set as \<and> c>0}"
by(force simp: lbounds_def split:list.splits atom.splits if_splits)
lemma set_ubounds:
 "set(ubounds as) = {(r/c, (-1/c) *\<^sub>s cs)|r c cs. Less r (c#cs) : set as \<and> c<0}"
by(force simp: ubounds_def split:list.splits atom.splits if_splits)
lemma set_ebounds:
  "set(ebounds as) = {(r/c, (-1/c) *\<^sub>s cs)|r c cs. Eq r (c#cs) : set as \<and> c\<noteq>0}"
by(force simp: ebounds_def split:list.splits atom.splits if_splits)


abbreviation EQ where
"EQ f xs \<equiv> {(r - \<langle>cs,xs\<rangle>)/c|r c cs. Eq r (c#cs) : set(R.atoms\<^isub>0 f) \<and> c\<noteq>0}"
abbreviation LB where
"LB f xs \<equiv> {(r - \<langle>cs,xs\<rangle>)/c|r c cs. Less r (c#cs) : set(R.atoms\<^isub>0 f) \<and> c>0}"
abbreviation UB where
"UB f xs \<equiv> {(r - \<langle>cs,xs\<rangle>)/c|r c cs. Less r (c#cs) : set(R.atoms\<^isub>0 f) \<and> c<0}"


fun asubst :: "real * real list \<Rightarrow> atom \<Rightarrow> atom" where
"asubst (r,cs) (Less s (d#ds)) = Less (s - d*r) (d *\<^sub>s cs + ds)" |
"asubst (r,cs) (Eq s (d#ds)) = Eq (s - d*r) (d *\<^sub>s cs + ds)" |
"asubst (r,cs) (Less s []) = Less s []" |
"asubst (r,cs) (Eq s []) = Eq s []"

abbreviation "subst \<phi> rcs \<equiv> map\<^bsub>fm\<^esub> (asubst rcs) \<phi>"

definition eval :: "real * real list \<Rightarrow> real list \<Rightarrow> real" where
"eval rcs xs = fst rcs + \<langle>snd rcs,xs\<rangle>"

lemma I_asubst:
 "I\<^isub>R (asubst t a) xs = I\<^isub>R a (eval t xs # xs)"
proof(cases a)
  case (Less r cs)
  thus ?thesis by(cases t, cases cs,
    simp_all add:eval_def right_distrib iprod_left_add_distrib iprod_assoc)
    arith
next
  case (Eq r cs)
  thus ?thesis
    by(cases t, cases cs, simp_all add:eval_def right_distrib iprod_left_add_distrib iprod_assoc)
      arith
qed

lemma I_subst:
  "qfree \<phi> \<Longrightarrow> R.I (subst \<phi> t) xs = R.I \<phi> (eval t xs # xs)"
by(induct \<phi>)(simp_all add:I_asubst)
lemma I_subst_pretty:
  "qfree \<phi> \<Longrightarrow> R.I (subst \<phi> (r,cs)) xs = R.I \<phi> ((r + \<langle>cs,xs\<rangle>) # xs)"
by(simp add:I_subst eval_def)


fun min_inf :: "atom fm \<Rightarrow> atom fm" ("inf\<^isub>-") where
"inf\<^isub>- (And \<phi>\<^isub>1 \<phi>\<^isub>2) = and (inf\<^isub>- \<phi>\<^isub>1) (inf\<^isub>- \<phi>\<^isub>2)" |
"inf\<^isub>- (Or \<phi>\<^isub>1 \<phi>\<^isub>2) = or (inf\<^isub>- \<phi>\<^isub>1) (inf\<^isub>- \<phi>\<^isub>2)" |
"inf\<^isub>- (Atom(Less r (c#cs))) =
  (if c<0 then TrueF else if c>0 then FalseF else Atom(Less r cs))" |
"inf\<^isub>- (Atom(Eq r (c#cs))) = (if c=0 then Atom(Eq r cs) else FalseF)" |
"inf\<^isub>- \<phi> = \<phi>"

fun plus_inf :: "atom fm \<Rightarrow> atom fm" ("inf\<^isub>+") where
"inf\<^isub>+ (And \<phi>\<^isub>1 \<phi>\<^isub>2) = and (inf\<^isub>+ \<phi>\<^isub>1) (inf\<^isub>+ \<phi>\<^isub>2)" |
"inf\<^isub>+ (Or \<phi>\<^isub>1 \<phi>\<^isub>2) = or (inf\<^isub>+ \<phi>\<^isub>1) (inf\<^isub>+ \<phi>\<^isub>2)" |
"inf\<^isub>+ (Atom(Less r (c#cs))) =
  (if c>0 then TrueF else if c<0 then FalseF else Atom(Less r cs))" |
"inf\<^isub>+ (Atom(Eq r (c#cs))) = (if c=0 then Atom(Eq r cs) else FalseF)" |
"inf\<^isub>+ \<phi> = \<phi>"

lemma qfree_min_inf: "qfree \<phi> \<Longrightarrow> qfree(inf\<^isub>- \<phi>)"
by(induct \<phi> rule:min_inf.induct) simp_all

lemma qfree_plus_inf: "qfree \<phi> \<Longrightarrow> qfree(inf\<^isub>+ \<phi>)"
by(induct \<phi> rule:plus_inf.induct) simp_all

lemma min_inf:
  "nqfree f \<Longrightarrow> \<exists>x. \<forall>y\<le>x. R.I (inf\<^isub>- f) xs = R.I f (y # xs)"
  (is "_ \<Longrightarrow> \<exists>x. ?P f x")
proof(induct f)
  case (Atom a)
  show ?case
  proof (cases a)
    case (Less r cs)
    show ?thesis
    proof(cases cs)
      case Nil thus ?thesis using Less by simp
    next
      case (Cons c cs)
      { assume "c=0" hence ?thesis using Less Cons by simp }
      moreover
      { assume "c<0"
	hence "?P (Atom a) ((r - \<langle>cs,xs\<rangle> + 1)/c)" using Less Cons
	  by(auto simp add: field_simps)
	hence ?thesis .. }
      moreover
      { assume "c>0"
	hence "?P (Atom a) ((r - \<langle>cs,xs\<rangle> - 1)/c)" using Less Cons
	  by(auto simp add: field_simps)
	hence ?thesis .. }
      ultimately show ?thesis by force
    qed
  next
    case (Eq r cs)
    show ?thesis
    proof(cases cs)
      case Nil thus ?thesis using Eq by simp
    next
      case (Cons c cs)
      { assume "c=0" hence ?thesis using Eq Cons by simp }
      moreover
      { assume "c<0"
	hence "?P (Atom a) ((r - \<langle>cs,xs\<rangle> + 1)/c)" using Eq Cons
	  by(auto simp add: field_simps)
	hence ?thesis .. }
      moreover
      { assume "c>0"
	hence "?P (Atom a) ((r - \<langle>cs,xs\<rangle> - 1)/c)" using Eq Cons
	  by(auto simp add: field_simps)
	hence ?thesis .. }
      ultimately show ?thesis by force
    qed
  qed
next
  case (And f1 f2)
  then obtain x1 x2 where "?P f1 x1" "?P f2 x2" by fastsimp+
  hence "?P (And f1 f2) (min x1 x2)" by(force simp:and_def)
  thus ?case ..
next
  case (Or f1 f2)
  then obtain x1 x2 where "?P f1 x1" "?P f2 x2" by fastsimp+
  hence "?P (Or f1 f2) (min x1 x2)" by(force simp:or_def)
  thus ?case ..
qed simp_all

lemma plus_inf:
  "nqfree f \<Longrightarrow> \<exists>x. \<forall>y\<ge>x. R.I (inf\<^isub>+ f) xs = R.I f (y # xs)"
  (is "_ \<Longrightarrow> \<exists>x. ?P f x")
proof(induct f)
  case (Atom a)
  show ?case
  proof (cases a)
    case (Less r cs)
    show ?thesis
    proof(cases cs)
      case Nil thus ?thesis using Less by simp
    next
      case (Cons c cs)
      { assume "c=0" hence ?thesis using Less Cons by simp }
      moreover
      { assume "c<0"
	hence "?P (Atom a) ((r - \<langle>cs,xs\<rangle> - 1)/c)" using Less Cons
	  by(auto simp add: field_simps)
	hence ?thesis .. }
      moreover
      { assume "c>0"
	hence "?P (Atom a) ((r - \<langle>cs,xs\<rangle> + 1)/c)" using Less Cons
	  by(auto simp add: field_simps)
	hence ?thesis .. }
      ultimately show ?thesis by force
    qed
  next
    case (Eq r cs)
    show ?thesis
    proof(cases cs)
      case Nil thus ?thesis using Eq by simp
    next
      case (Cons c cs)
      { assume "c=0" hence ?thesis using Eq Cons by simp }
      moreover
      { assume "c<0"
	hence "?P (Atom a) ((r - \<langle>cs,xs\<rangle> - 1)/c)" using Eq Cons
	  by(auto simp add: field_simps)
	hence ?thesis .. }
      moreover
      { assume "c>0"
	hence "?P (Atom a) ((r - \<langle>cs,xs\<rangle> + 1)/c)" using Eq Cons
	  by(auto simp add: field_simps)
	hence ?thesis .. }
      ultimately show ?thesis by force
    qed
  qed
next
  case (And f1 f2)
  then obtain x1 x2 where "?P f1 x1" "?P f2 x2" by fastsimp+
  hence "?P (And f1 f2) (max x1 x2)" by(force simp:and_def)
  thus ?case ..
next
  case (Or f1 f2)
  then obtain x1 x2 where "?P f1 x1" "?P f2 x2" by fastsimp+
  hence "?P (Or f1 f2) (max x1 x2)" by(force simp:or_def)
  thus ?case ..
qed simp_all


declare [[simp_depth_limit = 2]]

lemma LBex:
 "\<lbrakk> nqfree f; R.I f (x#xs); \<not>R.I (inf\<^isub>- f) xs; x \<notin> EQ f xs \<rbrakk>
  \<Longrightarrow> \<exists>l\<in> LB f xs. l < x"
apply(induct f)
apply simp
apply simp
apply(case_tac a)
 apply(simp add: depends\<^isub>R_def split:if_splits list.splits)
 apply(simp add: field_simps)
apply (fastsimp simp add: depends\<^isub>R_def split:if_splits list.splits)
apply fastsimp
apply fastsimp
apply simp
apply simp
done


lemma UBex:
 "\<lbrakk> nqfree f; R.I f (x#xs); \<not>R.I (inf\<^isub>+ f) xs; x \<notin> EQ f xs \<rbrakk>
  \<Longrightarrow> \<exists>u\<in> UB f xs. x < u"
apply(induct f)
apply simp
apply simp
apply(case_tac a)
 apply(simp add: depends\<^isub>R_def split:if_splits list.splits)
 apply(simp add: field_simps)
apply (fastsimp simp add: depends\<^isub>R_def split:if_splits list.splits)
apply fastsimp
apply fastsimp
apply simp
apply simp
done

declare [[simp_depth_limit = 50]]

lemma finite_LB: "finite(LB f xs)"
proof -
  have "LB f xs = (\<lambda>(r,cs). r + \<langle>cs,xs\<rangle>) ` set(lbounds(R.atoms\<^isub>0 f))"
    by (force simp:set_lbounds image_def field_simps iprod_assoc)
  thus ?thesis by simp
qed

lemma finite_UB: "finite(UB f xs)"
proof -
  have "UB f xs = (\<lambda>(r,cs). r + \<langle>cs,xs\<rangle>) ` set(ubounds(R.atoms\<^isub>0 f))"
    by (force simp:set_ubounds image_def field_simps iprod_assoc)
  thus ?thesis by simp
qed


end
