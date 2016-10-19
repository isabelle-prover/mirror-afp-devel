(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Real Algebraic Numbers\<close>

text \<open>Whereas we previously only proved the closure properties of algebraic numbers, this
  theory adds the numeric computations that are required to separate the roots, and to
  pick unique representatives of algebraic numbers. 

  The development is split into three major parts. First, an ambiguous representation of 
  algebraic numbers is used, afterwards another layer is used which contains a unique
  representation of an algebraic real number, with special treatment of rational numbers, 
  and finally, a quotient type is created modulo the equivalence.
  
  The theory also contains a code-setup to implement real numbers via real algebraic numbers.\<close>


text \<open>The results are taken from the textbook \cite[pages 329ff]{AlgNumbers}.
\<close>


theory Real_Algebraic_Numbers
imports 
  "../Abstract-Rewriting/SN_Order_Carrier"
  "../Deriving/Comparator_Generator/Compare_Rat"
  "../Deriving/Comparator_Generator/Compare_Real"
  "../Jordan_Normal_Form/Gauss_Jordan_IArray_Impl"
  Algebraic_Numbers
  Sturm_Rat
begin

(* **************************************************************** *)
subsection \<open>Real Algebraic Numbers -- Innermost Layer\<close>

text \<open>We represent a real algebraic number as follows: 
  None: 0;
  Some (ri,p,l,r): the unique root of p in the interval [l,r], where l and r have the 
    same sign and are non-zero; ri is the root-information to compute the nr of roots of p in
    certain intervals; we always assume that p is normalized, i.e.,
    p is the unique irreducible and monic polynomial which represents the algebraic number.
    

  This representation clearly admits duplicate representations for the same number, e.g.
  Some (...,x-3, 3,3) is equivalent to Some (...,x-3,2,10).\<close>

subsubsection \<open>Basic Definitions\<close>

definition unique_root :: "rat poly \<times> rat \<times> rat \<Rightarrow> bool" where
  "unique_root plr \<equiv> (\<exists>! x. root_cond plr x)"

definition the_unique_root :: "rat poly \<times> rat \<times> rat \<Rightarrow> real" where
  "the_unique_root plr \<equiv> (THE x. root_cond plr x)"

lemma the_unique_root: assumes ur: "unique_root (p,l,r)"
  shows "of_rat l \<le> the_unique_root (p,l,r)" "the_unique_root (p,l,r) \<le> of_rat r"
    "rpoly p (the_unique_root (p,l,r)) = 0"
    "root_cond (p,l,r) (the_unique_root (p,l,r))"
    "root_cond (p,l,r) y \<Longrightarrow> the_unique_root (p,l,r) = y"
proof -
  let ?x = "the_unique_root (p,l,r)"
  from ur[unfolded unique_root_def] have ex1: "\<exists>! x. root_cond (p,l,r) x" .
  from ex1 show x: "root_cond (p,l,r) ?x" unfolding the_unique_root_def
    by (rule theI')
  thus "of_rat l \<le> ?x" "?x \<le> of_rat r" "rpoly p ?x = 0" unfolding root_cond_def by auto
  from x ex1 show "root_cond (p,l,r) y \<Longrightarrow> ?x = y" by auto
qed

lemmas unique_root_defs = unique_root_def the_unique_root_def

type_synonym rai_intern_flat = "root_info \<times> rat poly \<times> rat \<times> rat"
type_synonym rai_intern = "rai_intern_flat option"


definition poly_cond :: "rat poly \<Rightarrow> bool" where
  "poly_cond p = (monic p \<and> irreducible p)"

lemma poly_cond_D: "poly_cond p \<Longrightarrow> irreducible p \<and> monic p \<and> root_free p \<and> square_free p"
  unfolding poly_cond_def using irreducible_root_free irreducible_square_free by auto

lemma poly_cond_I: "monic p \<Longrightarrow> irreducible p \<Longrightarrow> poly_cond p"
  by (auto simp: poly_cond_def)

definition rai_cond :: "rai_intern \<Rightarrow> bool" where
  "rai_cond plr = (case plr of Some (ri,p,l,r) \<Rightarrow> 
    unique_root (p,l,r) \<and> p \<noteq> 0 \<and> sgn l = sgn r \<and> sgn r \<noteq> 0 \<and> root_info_cond ri p 
    \<and> poly_cond p | None \<Rightarrow> True)"

lemma rai_cond_None[simp]: "rai_cond None = True" unfolding rai_cond_def by auto

definition rai_real :: "rai_intern \<Rightarrow> real" where
  "rai_real oplr = (case oplr of Some (cr,plr) \<Rightarrow> the_unique_root plr | None \<Rightarrow> 0)"

lemma rai_real_None[simp]: "rai_real None = 0" unfolding rai_real_def by auto

lemma rai_cond_realI: assumes "root_cond (p,l,r) x" "p \<noteq> 0" "sgn l = sgn r" "sgn r \<noteq> 0"
  and "\<And> y. root_cond (p,l,r) y \<Longrightarrow> x = y"
  and "root_info_cond ri p"
  and "poly_cond p"
  shows "rai_cond (Some (ri,p,l,r)) \<and> rai_real (Some (ri,p,l,r)) = x"
  unfolding rai_cond_def rai_real_def option.simps unique_root_defs split
  by (intro conjI ex1I[of _ x], insert assms, blast+)

typedef real_alg_intern = "Collect rai_cond"
  by (intro exI[of _ None], auto)

setup_lifting type_definition_real_alg_intern

lift_definition real_of_rai :: "real_alg_intern \<Rightarrow> real" is rai_real .

lemma rai_condD: assumes "rai_cond (Some (ri,p,l,r))"
  shows "root_cond (p,l,r) (rai_real (Some (ri,p,l,r)))"
    "sgn l = sgn r" "rai_real (Some (ri,p,l,r)) \<noteq> 0" "sgn r \<noteq> 0" "p \<noteq> 0" 
    "sgn (rai_real (Some (ri,p,l,r))) = of_rat (sgn r)"
    "unique_root (p,l,r)"
    "\<And> y. root_cond (p,l,r) y \<Longrightarrow> rai_real (Some (ri,p,l,r)) = y"
    "root_info_cond ri p"
    "poly_cond p"
proof -
  let ?p = "\<lambda> x. rpoly p x = 0 \<and> real_of_rat l \<le> x \<and> x \<le> real_of_rat r"
  let ?x = "rai_real (Some (ri,p,l,r))"
  let ?l = "of_rat l :: real"
  let ?r = "of_rat r :: real"
  from assms[unfolded rai_cond_def split] have ur: "unique_root (p,l,r)"
    and sgn: "sgn l = sgn r" "sgn r \<noteq> 0" and p: "p \<noteq> 0" and cr: "root_info_cond ri p" 
    and "poly_cond p" by auto
  show "poly_cond p" by fact    
  show "unique_root (p,l,r)" "root_info_cond ri p" by fact+
  note ur = the_unique_root[OF ur]
  from ur(1-4) have x: "rpoly p ?x = 0" and bnd: "?l \<le> ?x" "?x \<le> ?r"
    unfolding rai_real_def split by auto
  from ur(4) show "root_cond (p,l,r) ?x" unfolding rai_real_def by auto 
  show "sgn l = sgn r" "sgn r \<noteq> 0" "p \<noteq> 0" by fact+
  {
    assume "?x = 0"
    with bnd have "?l \<le> 0" "?r \<ge> 0" by auto
    hence "l \<le> 0" "r \<ge> 0" by auto
    with `sgn l = sgn r` `sgn r \<noteq> 0` have False unfolding sgn_rat_def by (auto split: if_splits)
  }
  thus "?x \<noteq> 0" by auto
  show "sgn ?x = of_rat (sgn r)"
  proof (cases "?x > 0")
    case True
    with bnd(2) have "0 < ?r" by arith
    thus ?thesis using True by simp
  next
    case False
    with `?x \<noteq> 0` have x: "?x < 0" by auto
    with bnd(1) have "?l < 0" by arith
    thus ?thesis unfolding `sgn l = sgn r`[symmetric] using x by simp
  qed
  from ur(5)
  show "\<And> y. root_cond (p,l,r) y \<Longrightarrow> ?x = y"
    unfolding rai_real_def by auto
qed

(* ********************** *)
subsubsection \<open>Embedding of Rational Numbers\<close>

definition poly_rat_root_info :: "rat \<Rightarrow> root_info" where
  "poly_rat_root_info x \<equiv> Root_Info (\<lambda> a b. if a \<le> x \<and> x \<le> b then 1 else 0) (\<lambda> a. if x \<le> a then 1 else 0)"

lemma poly_rat_root_info[simp]: "root_info_cond (poly_rat_root_info x) (poly_rat x)"
proof -
  have *: "\<And> a. {xa. xa = real_of_rat x \<and> xa \<le> real_of_rat a} = (if x \<le> a then {real_of_rat x} else {})" 
    by (auto split: if_splits simp: of_rat_less_eq)
  {
    fix a b
    have "{y. root_cond (poly_rat x,a,b) y} = {of_rat x} \<inter> {y. of_rat a \<le> y \<and> y \<le> of_rat b}" (is "?l = _")
      unfolding root_cond_def split by auto
    also have "\<dots> = (if a \<le> x \<and> x \<le> b then {of_rat x} else {})" (is "_ = ?r")
      by (auto simp: of_rat_less_eq)
    finally have "?l = ?r" .
  } note id = this
  show ?thesis unfolding root_info_cond_def id poly_rat_root_info_def using * by auto
qed

definition of_rat_rai_fun :: "rat \<Rightarrow> rai_intern" where
  "of_rat_rai_fun \<equiv> \<lambda> x. if x = 0 then None else Some (poly_rat_root_info x, poly_rat x,x,x)"

lemma of_rat_rai_main: assumes y: "y = of_rat_rai_fun x"
  shows "rai_cond y \<and> (rai_real y = of_rat x)"
  unfolding y of_rat_rai_fun_def
  by (auto simp: rai_real_def rai_cond_def sgn_rat_def unique_root_defs root_cond_def intro: poly_cond_I)

lift_definition of_rat_rai :: "rat \<Rightarrow> real_alg_intern" is of_rat_rai_fun
  by (insert of_rat_rai_main, auto)

lemma of_rat_rai: "real_of_rai (of_rat_rai x) = of_rat x"
  by (transfer, insert of_rat_rai_main, auto)

(* ********************** *)
subsubsection \<open>Sign\<close>

lift_definition sgn_rai :: "real_alg_intern \<Rightarrow> rat" is
  "\<lambda> x. case x of None \<Rightarrow> 0 | Some (ri,p,l,r) \<Rightarrow> sgn r"  .

lemma sgn_rai: "real_of_rat (sgn_rai x) = sgn (real_of_rai x)"
  by (transfer, case_tac "x", insert of_rat_rai_main rai_condD, auto)

lemma sgn_rai_inj: "real_of_rai x = real_of_rai y \<Longrightarrow> sgn_rai x = sgn_rai y"
proof (transfer, goal_cases)
  case (1 x y)
  show ?case
  proof (cases x)
    case None note x = this
    show ?thesis
    proof (cases y)
      case None note y = this
      show ?thesis using 1 x y by auto
    next
      case (Some y) note y = this
      show ?thesis using rai_condD 1 x y by (cases y, auto)
    qed
  next
    case (Some x) note x = this
    show ?thesis
    proof (cases y)
      case None note y = this
      show ?thesis using rai_condD 1 x y by (cases x, auto)
    next
      case (Some y) note y = this
      obtain ri1 p1 l1 r1 where xt: "x = (ri1,p1,l1,r1)" by (cases x, auto)
      obtain ri2 p2 l2 r2 where yt: "y = (ri2,p2,l2,r2)" by (cases y, auto)
      from 1 have "rai_cond (Some x)" unfolding x by auto
      from rai_condD(6)[OF this[unfolded xt]] xt
      have s1: "real_of_rat (sgn r1) = sgn (rai_real (Some x))" by simp
      from 1 have "rai_cond (Some y)" unfolding y by auto
      from rai_condD(6)[OF this[unfolded yt]] yt
      have s2: "real_of_rat (sgn r2) = sgn (rai_real (Some y))" by simp
      from s1 s2[symmetric] 1(3)[unfolded x y] have "sgn r1 = sgn r2" by simp
      thus ?thesis using x y xt yt by auto
    qed
  qed
qed

(* ********************** *)
subsubsection \<open>Normalization: Irreducible Polynomial, Bounds Close Together\<close>

lemma unique_root_non_zero_lr: assumes ur: "unique_root (p,l,r)"
  shows "l \<le> r" "l < r \<Longrightarrow> p \<noteq> 0"
proof -
  let ?l = "real_of_rat l"
  let ?r = "real_of_rat r"
  let ?P = "\<lambda> x. ?l \<le> x \<and> x \<le> ?r \<and> rpoly p x = 0"
  from ur[unfolded unique_root_def root_cond_def split]
  have ex1: "\<exists>! x. ?P x" by auto
  then obtain x where bnd: "?l \<le> x" "x \<le> ?r" and rt: "rpoly p x = 0" by auto
  from bnd have "?l \<le> ?r" by linarith
  thus "l \<le> r" by (simp add: of_rat_less_eq)
  assume "l < r"
  hence lr: "?l < ?r" by (simp add: of_rat_less)
  show "p \<noteq> 0"
  proof
    assume "p = 0"    
    hence "rpoly p ?l = 0" "rpoly p ?r = 0" by auto
    with lr have "?P ?l" "?P ?r" by auto
    with ex1 have "?l = ?r" by blast
    with lr show False by auto
  qed
qed

lemma eval_poly_id[simp]: "eval_poly id = poly" (is "?l = ?r")
  by (intro ext, unfold eval_poly_def, auto)

lemma unique_root_sub_interval: assumes ur: "unique_root (p,l,r)"
  and rc: "root_cond (p,l',r') (the_unique_root (p,l,r))"
  and between: "l \<le> l'" "r' \<le> r"
  shows "unique_root (p,l',r')" "the_unique_root (p,l',r') = the_unique_root (p,l,r)" 
proof -
  from between have ord: "real_of_rat l \<le> of_rat l'" "real_of_rat r' \<le> of_rat r" 
    by (auto simp: of_rat_less_eq)
  show ur': "unique_root (p,l',r')" unfolding unique_root_def
  proof (rule, rule rc)
    fix y
    assume "root_cond (p,l',r') y"
    with ord have "root_cond (p,l,r) y" unfolding root_cond_def by auto
    from the_unique_root(5)[OF ur this] show "y = the_unique_root (p,l,r)" by simp
  qed
  from the_unique_root(5)[OF ur' rc] 
  show "the_unique_root (p,l',r') = the_unique_root (p,l,r)" by simp
qed

lemma rai_cond_sub_interval: assumes rc: "rai_cond (Some (ri,p,l,r))"
  and sub: "root_cond (p,l',r') (the_unique_root (p,l,r))"
  and between: "l \<le> l'" "r' \<le> r"
  shows "rai_cond (Some (ri,p,l',r'))" "rai_real (Some (ri,p,l',r')) = rai_real (Some (ri,p,l,r))"  
proof -
  let ?r = real_of_rat
  note rcD = rai_condD[OF rc]
  from unique_root_sub_interval[OF rcD(7) sub between]
  have ur: "unique_root (p, l', r')" and id: "the_unique_root (p, l', r') = the_unique_root (p, l, r)" .
  show "rai_real (Some (ri,p,l',r')) = rai_real (Some (ri,p,l,r))"
    using id by (simp add: rai_real_def)
  from rcD(1)[unfolded root_cond_def split] have "?r l \<le> ?r r" by auto
  hence lr: "l \<le> r" by (auto simp: of_rat_less_eq)
  from the_unique_root(1,2)[OF ur] have "?r l' \<le> ?r r'" by auto
  hence lr': "l' \<le> r'" by (auto simp: of_rat_less_eq)
  have "sgn l' = sgn r' \<and> sgn r' \<noteq> 0"
  proof (cases "r < 0")
    case True
    with lr lr' between have "l < 0" "l' < 0" "r' < 0" "r < 0" by auto
    thus ?thesis unfolding sgn_rat_def by auto
  next
    case False
    with rcD(4) have "sgn r = 1" unfolding sgn_rat_def by (cases "r = 0", auto)
    with rcD(2) have "sgn l = 1" by simp
    hence l: "l > 0" unfolding sgn_rat_def by (cases "l = 0"; cases "l < 0"; auto)
    with lr lr' between have "l > 0" "l' > 0" "r' > 0" "r > 0" by auto
    thus ?thesis unfolding sgn_rat_def by auto
  qed
  thus "rai_cond (Some (ri,p,l',r'))"
    unfolding rai_cond_def
    by (simp add: ur rcD(5,9,10))
qed

context 
  fixes cr :: "rat \<Rightarrow> rat \<Rightarrow> nat"
  and p :: "rat poly"
  and x :: "rat"
begin

definition tighten_poly_bounds :: "rat \<Rightarrow> rat \<Rightarrow> rat \<times> rat" where
  "tighten_poly_bounds l r = (let m = (l + r) / 2 in if cr m r = 0
     then (l,m) else (m,r))"

lemma tighten_poly_bounds: assumes res: "tighten_poly_bounds l r = (l',r')"
  and ur: "unique_root (p,l,r)"
  and ri: "root_info_cond ri p"
  and cr: "cr = root_info.l_r ri"
  shows "root_cond (p,l',r') (the_unique_root (p,l,r))" "l \<le> l'" "l' \<le> r'" "r' \<le> r" 
    "(r' - l') = (r - l) / 2"    
proof -
  let ?x = "the_unique_root (p,l,r)"
  let ?x' = "the_unique_root (p,l',r')"
  let ?m = "(l + r) / 2"
  note d = tighten_poly_bounds_def Let_def
  from unique_root_non_zero_lr[OF ur] have lr: "l \<le> r" "l < r \<Longrightarrow> p \<noteq> 0" by auto
  thus "l \<le> l'" "l' \<le> r'" "r' \<le> r" "(r' - l') = (r - l) / 2"
    using res unfolding d by (auto split: if_splits)
  note ur = the_unique_root[OF ur]
  show "root_cond (p,l',r') ?x"
  proof (cases "l = r")
    case True
    thus ?thesis using ur(4) res unfolding d by (auto split: if_splits)
  next
    case False
    with lr have p: "p \<noteq> 0" by auto
    from lr have "?m \<le> r" by auto
    note cr' = root_info_condD(1)[OF ri this, folded cr]
    let ?R = "Collect (root_cond (p, ?m, r))"
    show ?thesis
    proof (cases "cr ?m r = 0")
      case True
      with res have id: "l' = l" "r' = ?m" unfolding d by auto
      from True[unfolded cr'] have R0: "card ?R = 0" by auto
      from finite_rpoly_roots[OF p] have "finite ?R" unfolding root_cond_def[abs_def] by auto
      with R0 have R: "?R = {}" by auto
      from lr have le: "of_rat l \<le> real_of_rat ?m" "real_of_rat ?m \<le> of_rat r" 
        by (auto simp: of_rat_less_eq)
      from R le have "Collect (root_cond (p,l,r)) = Collect (root_cond (p,l,?m))" 
        unfolding root_cond_def[abs_def] split by auto
      with ur(4) have "root_cond (p,l,?m) ?x" by auto
      thus ?thesis unfolding id .
    next
      case False
      with res have id: "l' = ?m" "r' = r" unfolding d by auto
      from False[unfolded cr'] have "card ?R > 0" by auto 
      then obtain x where rc: "root_cond (p,?m,r) x" unfolding card_gt_0_iff by auto
      from lr have "real_of_rat l \<le> of_rat ?m" by (auto simp: of_rat_less_eq)
      with rc have "root_cond (p,l,r) x" unfolding root_cond_def by auto
      from ur(5)[OF this] have x: "x = ?x" by simp
      with rc show ?thesis unfolding id by auto
    qed
  qed
qed   

partial_function (tailrec) tighten_poly_bounds_epsilon :: "rat \<Rightarrow> rat \<Rightarrow> rat \<times> rat" where
  [code]: "tighten_poly_bounds_epsilon l r = (if r - l \<le> x then (l,r) else
    (case tighten_poly_bounds l r of (l',r') \<Rightarrow> tighten_poly_bounds_epsilon l' r'))"
    
partial_function (tailrec) tighten_poly_bounds_for_x :: "rat \<Rightarrow> rat \<Rightarrow> 
  rat \<times> rat" where 
  [code]: "tighten_poly_bounds_for_x l r = (if x < l \<or> r < x then (l, r) else
     (case tighten_poly_bounds l r of (l',r') \<Rightarrow> tighten_poly_bounds_for_x l' r'))"

lemma tighten_poly_bounds_epsilon: assumes ur: "unique_root (p,l,r)"
  and u: "u = the_unique_root (p,l,r)"
  and ri: "root_info_cond ri p"
  and cr: "cr = root_info.l_r ri"
  and res: "tighten_poly_bounds_epsilon l r = (l',r')"
  and x: "x > 0"
  shows "l \<le> l'" "r' \<le> r" "root_cond (p,l',r') u" "r' - l' \<le> x"
proof -
  let ?u = "the_unique_root (p,l,r)"
  def delta \<equiv> "x / 2"
  have delta: "delta > 0" unfolding delta_def using x by auto
  let ?dist = "\<lambda> (l,r). r - l"
  let ?rel = "inv_image {(x, y). 0 \<le> y \<and> delta_gt delta x y} ?dist"
  note SN = SN_inv_image[OF delta_gt_SN[OF delta], of ?dist]
  note simps = res[unfolded tighten_poly_bounds_for_x.simps[of l r]]
  let ?P = "\<lambda> (l,r). unique_root (p,l,r) \<longrightarrow> u = the_unique_root (p,l,r) 
    \<longrightarrow> tighten_poly_bounds_epsilon l r = (l',r') 
    \<longrightarrow> l \<le> l' \<and> r' \<le> r \<and> r' - l' \<le> x \<and> root_cond (p,l',r') u"
  have "?P (l,r)"
  proof (induct rule: SN_induct[OF SN])
    case (1 lr)
    obtain l r where lr: "lr = (l,r)" by force
    show ?case unfolding lr split
    proof (intro impI)
      assume ur: "unique_root (p, l, r)"
        and u: "u = the_unique_root (p, l, r)"
        and res: "tighten_poly_bounds_epsilon l r = (l', r')"
      note tur = the_unique_root[OF ur]
      note simps = tighten_poly_bounds_epsilon.simps[of l r]
      show "l \<le> l' \<and> r' \<le> r \<and> r' - l' \<le> x \<and> root_cond (p, l', r') u"
      proof (cases "r - l \<le> x")
        case True
        with res[unfolded simps] ur tur(4) u
        show ?thesis by auto
      next
        case False 
        hence x: "r - l > x" by auto
        let ?tight = "tighten_poly_bounds l r"
        obtain L R where tight: "?tight = (L,R)" by force
        note tighten = tighten_poly_bounds[OF tight ur ri cr]
        from unique_root_sub_interval[OF ur tighten(1-2,4)] have ur': "unique_root (p,L,R)"
          "u = the_unique_root (p,L,R)" unfolding u by auto
        from res[unfolded simps tight] False have "tighten_poly_bounds_epsilon L R = (l',r')" by auto
        note IH = 1[of ?tight, unfolded tight split lr, rule_format, OF _ ur' this]
        have "L \<le> l' \<and> r' \<le> R \<and> r' - l' \<le> x \<and> root_cond (p, l', r') u"
          by (rule IH, insert tighten False, auto simp: delta_gt_def delta_def)
        thus ?thesis using tighten by auto
      qed
    qed
  qed
  from this[unfolded split u, rule_format, OF ur refl res] 
  show "l \<le> l'" "r' \<le> r" "root_cond (p,l',r') u" "r' - l' \<le> x" using u by auto
qed

lemma tighten_poly_bounds_for_x: assumes ur: "unique_root (p,l,r)"
  and x: "l \<le> x \<Longrightarrow> x \<le> r \<Longrightarrow> poly p x \<noteq> 0"
  and u: "u = the_unique_root (p,l,r)"
  and ri: "root_info_cond ri p"
  and cr: "cr = root_info.l_r ri"
  and res: "tighten_poly_bounds_for_x l r = (l',r')"
  shows "l \<le> l'" "l' \<le> r'" "r' \<le> r" "root_cond (p,l',r') u" "\<not> (l' \<le> x \<and> x \<le> r')"
proof -
  let ?u = "the_unique_root (p,l,r)"
  let ?x = "real_of_rat x"
  def delta \<equiv> "abs ((u - ?x) / 2)"
  let ?p = "real_of_rat_poly p"
  note ru = the_unique_root(1-3)[OF ur]
  {
    assume "u = ?x"
    from ru[unfolded this[unfolded u] of_rat_less_eq rpoly.eval_poly_poly[where 'a = real]] 
      x have False by auto
  }
  hence delta: "delta > 0" unfolding delta_def by auto
  let ?dist = "\<lambda> (l,r). real_of_rat (r - l)"
  let ?rel = "inv_image {(x, y). 0 \<le> y \<and> delta_gt delta x y} ?dist"
  note SN = SN_inv_image[OF delta_gt_SN[OF delta], of ?dist]
  note simps = res[unfolded tighten_poly_bounds_for_x.simps[of l r]]
  let ?P = "\<lambda> (l,r). unique_root (p,l,r) \<longrightarrow> u = the_unique_root (p,l,r) 
    \<longrightarrow> tighten_poly_bounds_for_x l r = (l',r') 
    \<longrightarrow> l \<le> l' \<and> r' \<le> r \<and> \<not> (l' \<le> x \<and> x \<le> r') \<and> root_cond (p,l',r') u"
  have "?P (l,r)"
  proof (induct rule: SN_induct[OF SN])
    case (1 lr)
    obtain l r where lr: "lr = (l,r)" by force
    let ?l = "real_of_rat l"
    let ?r = "real_of_rat r"
    show ?case unfolding lr split
    proof (intro impI)
      assume ur: "unique_root (p, l, r)"
        and u: "u = the_unique_root (p, l, r)"
        and res: "tighten_poly_bounds_for_x l r = (l', r')"
      note tur = the_unique_root[OF ur]
      note simps = tighten_poly_bounds_for_x.simps[of l r]
      show "l \<le> l' \<and> r' \<le> r \<and> \<not> (l' \<le> x \<and> x \<le> r') \<and> root_cond (p, l', r') u"
      proof (cases "x < l \<or> r < x")
        case True
        with res[unfolded simps] ur tur(4) u
        show ?thesis by auto
      next
        case False 
        hence x: "?l \<le> ?x" "?x \<le> ?r" 
          by (auto simp: of_rat_less_eq)
        let ?tight = "tighten_poly_bounds l r"
        obtain L R where tight: "?tight = (L,R)" by force
        note tighten = tighten_poly_bounds[OF tight ur ri cr]
        from unique_root_sub_interval[OF ur tighten(1-2,4)] have ur': "unique_root (p,L,R)"
          "u = the_unique_root (p,L,R)" unfolding u by auto
        from res[unfolded simps tight] False have "tighten_poly_bounds_for_x L R = (l',r')" by auto
        note IH = 1[of ?tight, unfolded tight split lr, rule_format, OF _ ur' this]
        let ?DIFF = "real_of_rat (R - L)" let ?diff = "real_of_rat (r - l)"
        have diff0: "0 \<le> ?DIFF" using tighten(3)
          by (metis cancel_comm_monoid_add_class.diff_cancel diff_right_mono of_rat_less_eq rpoly.hom_zero)
        have *: "r - l - (r - l) / 2 = (r - l) / 2" by (auto simp: field_simps)
        have "delta_gt delta ?diff ?DIFF = (abs (u - of_rat x) \<le> real_of_rat (r - l) * 1)"
          unfolding delta_gt_def tighten(5) delta_def of_rat_diff[symmetric] * by simp
        also have "real_of_rat (r - l) * 1 = ?r - ?l" 
          unfolding of_rat_divide of_rat_mult of_rat_diff by auto
        also have "abs (u - of_rat x) \<le> ?r - ?l" using x tur(1-2)[folded u] by linarith
        finally have delta: "delta_gt delta ?diff ?DIFF" .
        have "L \<le> l' \<and> r' \<le> R \<and> \<not> (l' \<le> x \<and> x \<le> r') \<and> root_cond (p, l', r') u"
          by (rule IH, insert delta diff0, auto)
        with `l \<le> L` `R \<le> r` show ?thesis by auto
      qed
    qed
  qed
  from this[unfolded split u, rule_format, OF ur refl res] 
  show *: "l \<le> l'" "r' \<le> r" "root_cond (p,l',r') u" "\<not> (l' \<le> x \<and> x \<le> r')" unfolding u 
    by auto
  from *(3)[unfolded root_cond_def split] have "real_of_rat l' \<le> of_rat r'" by auto
  thus "l' \<le> r'" unfolding of_rat_less_eq .
qed
end

fun rai_normalize_poly_main :: "rat \<Rightarrow> rat \<Rightarrow> rat poly list \<Rightarrow> rai_intern_flat" where 
  "rai_normalize_poly_main l r (p # ps) = (let ri = count_roots_interval_rat p in
    if root_info.l_r ri l r = 0 then rai_normalize_poly_main l r ps 
    else (ri,p,l,r))"

definition rai_normalize_poly_flat :: "rai_intern_flat \<Rightarrow> rai_intern_flat" where
  "rai_normalize_poly_flat rai \<equiv> case rai of (ri,p,l,r) \<Rightarrow>
    rai_normalize_poly_main l r (factors_of_rat_poly p)"

definition real_alg_precision :: rat where
  "real_alg_precision \<equiv> inverse 8"

lemma real_alg_precision: "real_alg_precision > 0" 
  by code_simp

definition rai_normalize_bounds_flat :: "rat \<Rightarrow> rai_intern_flat \<Rightarrow> rai_intern_flat" where
  "rai_normalize_bounds_flat eps rai = (case rai of (ri,p,l,r) \<Rightarrow>
    let (l',r') = tighten_poly_bounds_epsilon (root_info.l_r ri) eps l r;
        fr = rat_of_int (floor r')
      in (if fr \<ge> l' \<and> poly p fr = 0 then (ri,p,fr,fr)
        else let
        (l'',r'') = tighten_poly_bounds_for_x (root_info.l_r ri) fr l' r'
    in (ri,p,l'',r'')))"

definition rai_normalize_bounds :: "rai_intern \<Rightarrow> rai_intern" where 
  "rai_normalize_bounds = map_option (rai_normalize_bounds_flat real_alg_precision)"

context
  fixes p q and l r :: rat
  assumes cong: "\<And> x. real_of_rat l \<le> x \<Longrightarrow> x \<le> of_rat r \<Longrightarrow> (rpoly p x = (0 :: real)) = (rpoly q x = 0)"
begin
lemma root_cond_cong: "root_cond (p,l,r) = root_cond (q,l,r)"
  by (intro ext, insert cong, auto simp: root_cond_def)

lemma the_unique_root_cong: 
  "the_unique_root (p,l,r) = the_unique_root (q,l,r)"
  unfolding the_unique_root_def root_cond_cong ..

lemma unique_root_cong: 
  "unique_root (p,l,r) = unique_root (q,l,r)"
  unfolding unique_root_def root_cond_cong ..
end

lemma rai_normalize_poly_flat: 
  assumes res: "rai_normalize_poly_flat (ri,p,l,r) = (ri',p',l',r')"
    and ur: "unique_root (p,l,r)" and p0: "p \<noteq> 0" and ri: "root_info_cond ri p"
  shows "unique_root (p',l,r)" "p' \<noteq> 0" "l' = l" "r' = r" 
    "poly_cond p'"
    "the_unique_root (p',l,r) = the_unique_root (p,l,r)" "root_info_cond ri' p'" "monic p'"
proof -
  note res = res[unfolded rai_normalize_poly_flat_def split]
  let ?y = "(ri',p',l',r')"
  have "unique_root (p',l,r) \<and> p' \<noteq> 0 \<and> l' = l \<and> r' = r 
    \<and> poly_cond p'
    \<and> the_unique_root (p',l,r) = the_unique_root (p,l,r) \<and> root_info_cond ri' p' \<and> monic p'"
  proof -
    obtain fs where fs: "factors_of_rat_poly p = fs" by auto
    from res fs have res: "rai_normalize_poly_main l r fs = ?y" by auto
    note fact = factors_of_rat_poly[OF fs]
    note fact = fact(1) fact(2-3)[OF p0]
    interpret rp: inj_ring_hom real_of_rat_poly by (rule rpoly.inj_ring_hom_map_poly)
    from ur have ur': "unique_root (p, l, r)" .
    let ?r = "real_of_rat r"
    let ?l = "real_of_rat l"
    def x \<equiv> "the_unique_root (p,l,r)"
    let ?prop = "\<lambda> ri q. root_info_cond ri q \<and> monic q 
      \<and> poly_cond q 
      \<and> x = the_unique_root (q,l,r) \<and> unique_root (q,l,r)
      \<and> rai_normalize_poly_main l r fs = 
        (ri,q,l,r)"
    note unique = the_unique_root[OF ur', folded x_def] 
    from unique(3) have "rpoly p x = 0" .
    from fact(3)[OF this] have ex1: "\<exists>!q. q \<in> set fs \<and> rpoly q x = 0" . 
    hence ex: "\<exists>q. q \<in> set fs \<and> rpoly q x = 0" by auto
    from fact(1-2) have "\<And> q. q \<in> set fs \<Longrightarrow>
      irreducible q \<and>
      monic q" 
      "\<And> q (x :: real). q \<in> set fs \<Longrightarrow> rpoly q x = 0 \<Longrightarrow> rpoly p x = 0"
      by auto
    with ex have "\<exists> ri q. ?prop ri q" 
    proof (induct fs)
      case (Cons f fs)
      def ri \<equiv> "count_roots_interval_rat f" 
      def cr \<equiv> "root_info.l_r ri"
      from Cons(3)[of f] have ptc: "poly_cond f" 
        and mon: "monic f" and p0: "f \<noteq> 0" 
        by (auto simp: poly_cond_def)
      from poly_cond_D(1)[OF ptc] have sf: "square_free f" by auto
      from unique(4)[unfolded root_cond_def] have "?l \<le> ?r" by auto
      hence lr: "l \<le> r" by (simp add: of_rat_less_eq)
      note cri = count_roots_interval_rat[OF sf, folded ri_def]
      note ri = root_info_condD[OF cri, folded cr_def]
      note cr_lr = ri(1)[OF lr]
      from finite_rpoly_roots[OF p0] have fin: "finite (Collect (root_cond (f, l, r)))" 
        unfolding root_cond_def[abs_def] by auto
      show ?case
      proof (cases "cr l r = 0")
        case True
        hence id: "rai_normalize_poly_main l r (f # fs)
          = rai_normalize_poly_main l r fs"
          by (simp add: cr_def ri_def)
        from True[unfolded cr_lr] fin have empty: "\<not> root_cond (f,l,r) x" by auto
        from Cons(2) empty unique(1-4) have "\<exists>q. q \<in> set fs \<and> rpoly q x = 0" by (auto simp: root_cond_def)
        from Cons(1)[OF this Cons(3)] Cons(4) show ?thesis unfolding id by auto
      next
        case False
        hence id: "rai_normalize_poly_main l r (f # fs)
          = (ri,f,l,r)"
          by (simp add: cr_def ri_def)
        from False have "cr l r > 0" by auto
        from this[unfolded cr_lr card_gt_0_iff] obtain y where rc: "root_cond (f,l,r) y" by auto
        {
          fix y
          assume y: "root_cond (f,l,r) y"
          hence rt: "rpoly f y = 0" unfolding root_cond_def by auto
          from Cons(4)[OF _ this] y have "root_cond (p,l,r) y" unfolding root_cond_def by auto
          from unique(5)[OF this] have "y = x" by simp
        } note un = this        
        from un[OF rc] rc have rc: "root_cond (f, l, r) x" by simp
        have ur: "unique_root (f, l, r)" unfolding unique_root_def
        proof
          fix z
          assume "root_cond (f,l,r) z"
          from un[OF rc] un[OF this] show "z = x" by simp
        qed (rule rc)
        from the_unique_root(5)[OF this rc]
        show ?thesis
          by (intro exI[of _ ri] exI[of _ f], unfold id, intro conjI,
          auto simp: cri mon ptc ur)
      qed
    qed simp
    then obtain ri q where main: "?prop ri q" by blast
    with res show ?thesis unfolding x_def by auto
  qed
  thus "unique_root (p',l,r)" "p' \<noteq> 0" "l' = l" "r' = r" 
    "poly_cond p'"
    "the_unique_root (p',l,r) = the_unique_root (p,l,r)" "root_info_cond ri' p'" "monic p'" by blast+
qed


lemma rai_normalize_poly_flat_rai_cond:   
  assumes rc: "rai_cond (Some x)" 
  defines res: "y \<equiv> rai_normalize_poly_flat x"
  assumes y: "y = (ri',p',l',r')"
  shows "rai_cond (Some y)" "rai_real (Some y) = rai_real (Some x)" 
    "monic p'"
proof -
  obtain ri p l r where x: "x = (ri,p,l,r)" by (cases x) auto
  with res x y have res: "rai_normalize_poly_flat (ri,p,l,r) = (ri',p',l',r')" by auto
  note rcD = rai_condD[OF rc[unfolded x]]
  from rcD(5) have p0: "p \<noteq> 0" .
  from rcD(2,4,10) rai_normalize_poly_flat[OF res rcD(7,5,9)]
  show "rai_cond (Some y)" "rai_real (Some y) = rai_real (Some x)" 
   "monic p'" unfolding y x 
   by (auto simp: rai_real_def rai_cond_def)
qed

lemma rai_normalize_bounds_flat: assumes eps: "eps > 0" and rc: "rai_cond (Some x)"
  defines y: "y \<equiv> rai_normalize_bounds_flat eps x"
  shows "rai_cond (Some y) \<and> (rai_real (Some y) = rai_real (Some x))"
proof -
  obtain ri p l r where x: "x = (ri,p,l,r)" by (cases x) auto
  note rc = rc[unfolded x]
  def cr \<equiv> "root_info.l_r ri"
  obtain l' r' where tb: "tighten_poly_bounds_epsilon cr eps l r = (l',r')" by force
  let ?fr = "rat_of_int (floor r')"
  obtain l'' r'' where tbx: "tighten_poly_bounds_for_x cr ?fr l' r' = (l'',r'')" by force
  from y[unfolded rai_normalize_bounds_flat_def x] tb tbx
  have y: "y = (if l' \<le> ?fr \<and> poly p ?fr = 0 then ( ri, p, ?fr, ?fr) else ( ri, p, l'', r''))" 
    by (auto simp: Let_def cr_def)
  note rcD = rai_condD[OF rc]
  from tighten_poly_bounds_epsilon[OF rcD(7) refl rcD(9) _ tb eps]
  have bnd: "l \<le> l'" "r' \<le> r" and rc': "root_cond (p, l', r') (the_unique_root (p, l, r))" 
    and eps: "r' - l' \<le> eps" (* currently not relevant for lemma *)
    by (auto simp: cr_def)
  note sub = rai_cond_sub_interval[OF rc rc' bnd]
  note rc = sub(1)
  note rcD = rai_condD[OF rc]
  show ?thesis
  proof (cases "l' \<le> ?fr \<and> poly p ?fr = 0")
    case False    
    hence y: "y = (ri,p,l'',r'')" unfolding y by auto
    from False have "l' \<le> ?fr \<Longrightarrow> ?fr \<le> r' \<Longrightarrow> poly p ?fr \<noteq> 0" by auto
    from tighten_poly_bounds_for_x[OF rcD(7) this refl rcD(9) _ tbx]
    have bnd: "l' \<le> l''" "r'' \<le> r'" and rc': "root_cond (p, l'', r'') (the_unique_root (p, l', r'))" 
      by (auto simp: cr_def)
    note sub' = rai_cond_sub_interval[OF rc rc' bnd]
    from sub sub'
    show ?thesis unfolding y x by auto
  next
    case True
    hence y: "y = (ri,p,?fr,?fr)" unfolding y by auto
    let ?r = real_of_rat
    from True have bnd: "l' \<le> ?fr" "?fr \<le> r'" by linarith+
    from True have "rpoly p (?r ?fr) = 0" unfolding rpoly.eval_poly_poly by simp
    hence rc': "root_cond (p,l',r') (?r ?fr)" using bnd unfolding root_cond_def split of_rat_less_eq by auto
    from rcD(8)[OF this] sub(2) x
    have rfr: "?r ?fr = the_unique_root (p,l',r')" by (auto simp: rai_real_def)
    from rc' have "root_cond (p,?fr,?fr) (the_unique_root (p,l',r'))"
      unfolding root_cond_def split rfr by auto
    note sub' = rai_cond_sub_interval[OF rc this bnd]
    from sub sub'
    show ?thesis unfolding y x by auto
  qed
qed

lemma rai_normalize_bounds: assumes x: "rai_cond x"
  shows "rai_cond (rai_normalize_bounds x) \<and> (rai_real (rai_normalize_bounds x) = rai_real x)" 
proof (cases x)
  case None
  thus ?thesis unfolding rai_normalize_bounds_def by auto
next
  case (Some xx)
  obtain ri p l r where xx: "xx = (ri,p,l,r)" (is "_ = ?res") by (cases xx, auto)
  let ?x = "Some ?res"
  have norm: "rai_normalize_bounds (Some xx) = Some (rai_normalize_bounds_flat real_alg_precision ?res)" 
    unfolding rai_normalize_bounds_def by (simp add: xx)
  from x have x: "rai_cond ?x" "rai_real ?x = rai_real x" 
    unfolding Some xx by auto
  from rai_normalize_bounds_flat[OF real_alg_precision x(1)] x(2-)
  show ?thesis unfolding Some rai_normalize_bounds_def xx by auto
qed

lift_definition normalize_bounds_rai :: "real_alg_intern \<Rightarrow> real_alg_intern" is rai_normalize_bounds
  using rai_normalize_bounds by auto

lemma normalize_bounds_rai[simp]: "real_of_rai (normalize_bounds_rai x) = real_of_rai x"
  by (transfer, insert rai_normalize_bounds, simp)

(* ********************* *)
subsubsection \<open>Comparisons\<close>

definition info_fun_rai :: "rai_intern \<Rightarrow> rat poly \<times> nat" where
  "info_fun_rai rai \<equiv> case rai of None \<Rightarrow> (poly_rat 0,1) 
    | Some (ri,p,l,r) \<Rightarrow> (p,root_info.inf_r ri r)"

definition poly_of_rai :: "rai_intern \<Rightarrow> rat poly" where
  "poly_of_rai rai \<equiv> case rai of None \<Rightarrow> poly_rat 0 
    | Some (ri,p,l,r) \<Rightarrow> p"

lift_definition info_rai :: "real_alg_intern \<Rightarrow> rat poly \<times> nat" is info_fun_rai .
lift_definition poly_rai :: "real_alg_intern \<Rightarrow> rat poly" is poly_of_rai .

lemma poly_rai_info_rai: "poly_rai rai = fst (info_rai rai)" 
proof (transfer, goal_cases)
  case (1 rai)
  show ?case by (cases rai, cases "the rai", auto simp: poly_of_rai_def info_fun_rai_def)
qed

lemma root_index_unique: assumes 
    1: "root_cond (p, l1, r1) x" "unique_root (p, l1, r1)"
  and 2: "root_cond (p, l2, r2) x" "unique_root (p, l2, r2)"
  shows "{x. x \<le> real_of_rat r1 \<and> rpoly p x = 0} = {x. x \<le> real_of_rat r2 \<and> rpoly p x = 0}"
proof -
  let ?r = "real_of_rat"
  let ?p = "map_poly ?r p"
  let ?set = "\<lambda> r. {x. x \<le> ?r r \<and> rpoly p x = 0}"
  {
    fix l1 r1 l2 r2
    assume 1: "root_cond (p, l1, r1) x" "unique_root (p, l1, r1)"
       and 2: "root_cond (p, l2, r2) x" "unique_root (p, l2, r2)"
       and r12: "r1 \<le> r2"
    note 11 = 1(1)[unfolded root_cond_def, unfolded split]
    note 22 = 2(1)[unfolded root_cond_def, unfolded split]
    let ?l1 = "?r l1"
    let ?l2 = "?r l2"
    let ?r1 = "?r r1"
    let ?r2 = "?r r2"
    from r12 have "?r1 \<le> ?r2" by (auto simp: of_rat_less_eq)
    hence sub: "?set r1 \<subseteq> ?set r2" by auto
    {
      fix y
      assume "y \<in> ?set r2 - ?set r1"
      hence rt: "rpoly p y = 0" and r2: "y \<le> ?r2" and r1: "\<not> y \<le> ?r1" by auto
      from r1 rt 11 have xy: "x < y" by auto
      {
        assume "?l2 \<le> y"
        with r2 rt have "root_cond (p, l2, r2) y" unfolding root_cond_def by auto
        with 2 have "x = y" unfolding unique_root_def by blast
        with xy have False by auto
      }
      hence l2: "y < ?l2" by force
      from 22 have "?l2 \<le> x" by auto
      with xy l2 have False by linarith
    }
    with sub have "?set r1 = ?set r2" by blast
  } note main = this
  have "r1 \<le> r2 \<or> r2 \<le> r1" by linarith
  with main[OF 1 2] main[OF 2 1, symmetric]
  show ?thesis by blast
qed

lemma root_index_unique_inv: assumes card: 
   "card {x. x \<le> real_of_rat r1 \<and> rpoly p x = 0} = 
    card {x. x \<le> real_of_rat r2 \<and> rpoly p x = 0}"
    and p: "p \<noteq> 0"
  and 1: "root_cond (p, l1, r1) (the_unique_root (p, l1, r1))" "unique_root (p, l1, r1)"
  and 2: "root_cond (p, l2, r2) (the_unique_root (p, l2, r2))" "unique_root (p, l2, r2)"
  shows "the_unique_root (p, l1, r1) = the_unique_root (p, l2, r2)"
proof -
  let ?r = "real_of_rat"
  let ?p = "map_poly ?r p"
  let ?set = "\<lambda> r. {x. x \<le> ?r r \<and> rpoly p x = 0}"
  let ?rt = "\<lambda> l r. the_unique_root (p, l, r)"
  from finite_rpoly_roots[OF p]
  have fin: "\<And> r. finite (?set r)" by auto
  {
    fix l1 r1 l2 r2 
    let ?l1 = "?r l1"
    let ?l2 = "?r l2"
    let ?r1 = "?r r1"
    let ?r2 = "?r r2"
    let ?x1 = "?rt l1 r1"
    let ?x2 = "?rt l2 r2"
    assume 1: "root_cond (p, l1, r1) ?x1" "unique_root (p, l1, r1)"
       and 2: "root_cond (p, l2, r2) ?x2" "unique_root (p, l2, r2)"
       and card: "card (?set r1) = card (?set r2)"
       and l12: "l1 \<le> l2"
    hence l12: "?l1 \<le> ?l2" by (auto simp: of_rat_less_eq)
    have "r1 \<le> r2 \<or> r2 \<le> r1" by linarith
    have "?r1 \<le> ?r2 \<or> ?r2 \<le> ?r1" by (auto simp: of_rat_less_eq)
    hence sub: "?set r1 \<subseteq> ?set r2 \<or> ?set r2 \<subseteq> ?set r1" by auto
    {
      assume "?set r1 \<noteq> ?set r2"
      with sub have "?set r1 \<subset> ?set r2 \<or> ?set r2 \<subset> ?set r1" by auto
      with psubset_card_mono[OF fin, of "?set r1" r2] 
        psubset_card_mono[OF fin, of "?set r2" r1] card have False by auto
    }
    hence id: "?set r1 = ?set r2" by auto
    note 22 = 2(1)[unfolded root_cond_def, unfolded split]
    from 22 l12 have x21: "?l1 \<le> ?x2" "?x2 \<le> ?r1" using id by auto
    with 22 have "root_cond (p, l1, r1) ?x2" unfolding root_cond_def by auto
    from the_unique_root(5)[OF 1(2) this]
    have "?rt l1 r1 = ?rt l2 r2" .
  } note main = this
  have "l1 \<le> l2 \<or> l2 \<le> l1" by linarith
  with main[OF 1 2 card] main[OF 2 1 card[symmetric], symmetric]  
  show ?thesis by blast
qed
  
 
lemma rai_info_fun: assumes 
    x: "rai_cond x" and y: "rai_cond y"
  shows "info_fun_rai x = info_fun_rai y \<Longrightarrow> rai_real x = rai_real y"
  "rai_real x = rai_real y \<Longrightarrow> info_fun_rai x = info_fun_rai y"
proof -
  let ?ri = info_fun_rai
  note d = info_fun_rai_def
  note rc = rai_condD
  let ?zinfo = "(poly_rat 0, 1)"
  {
    fix x
    assume x: "rai_cond x"
    have "?ri x = ?zinfo \<longleftrightarrow> rai_real x = 0"
    proof (cases x)
      case (Some tuple)
      obtain ri p l r where tuple: "tuple = (ri,p,l,r)" by (cases tuple, auto)
      let ?x = "rai_real (Some ( ri, p, l, r))"
      note id = Some[unfolded tuple]
      from rc(1-3)[OF x[unfolded id]]
      have rc: "root_cond (p, l, r) ?x"  and n0: "?x \<noteq> 0" by auto
      from id n0 have neq1: "rai_real x \<noteq> 0" by auto
      have ri: "?ri x = (p, root_info.inf_r ri r)" unfolding id d by simp
      from rc[unfolded root_cond_def] have 0: "rpoly p ?x = 0" by simp
      have "rpoly (poly_rat 0) ?x \<noteq> 0" using n0 by simp
      with 0 have neq2: "?ri x \<noteq> ?zinfo" unfolding ri by auto
      from neq1 neq2 show ?thesis by auto
    qed (auto simp: d)
  } note zero = this
  have "(?ri x = ?ri y \<longrightarrow> rai_real x = rai_real y) \<and> 
    (rai_real x = rai_real y \<longrightarrow> ?ri x = ?ri y)"
  proof (cases "rai_real x = 0")
    case True note x0 = this
    with zero[OF x] have x: "?ri x = ?zinfo" by auto
    show ?thesis
    proof (cases "rai_real y = 0")
      case True note y0 = this
      with zero[OF y] have y: "?ri y = ?zinfo" by auto
      show ?thesis using y0 x0 x y by auto
    next
      case False note y0 = this
      with zero[OF y] have y: "?ri y \<noteq> ?zinfo" by auto
      show ?thesis using y0 x0 x y by auto
    qed
  next
    case False note x0 = this
    with zero[OF x] have rifx: "?ri x \<noteq> ?zinfo" by auto
    show ?thesis
    proof (cases "rai_real y = 0")
      case True note y0 = this
      with zero[OF y] have y: "?ri y = ?zinfo" by auto
      show ?thesis using y0 x0 rifx y by auto
    next
      case False note y0 = this
      from x0 obtain t1 where xt: "x = Some t1" by (cases x, auto)
      from y0 obtain t2 where yt: "y = Some t2" by (cases y, auto)
      obtain ri1 p1 l1 r1 where t1: "t1 = (ri1,p1,l1,r1)" by (cases t1, auto)
      obtain ri2 p2 l2 r2 where t2: "t2 = (ri2,p2,l2,r2)" by (cases t2, auto)
      note x' = xt[unfolded t1]
      note y' = yt[unfolded t2]
      let ?x = "Some (ri1,p1,l1,r1)"
      let ?y = "Some (ri2,p2,l2,r2)"
      let ?n1 = "root_info.inf_r ri1"
      let ?n2 = "root_info.inf_r ri2"
      have rx: "?ri x = (p1,?n1 r1)" unfolding d x' by simp
      have ry: "?ri y = (p2,?n2 r2)" unfolding d y' by simp    
      let ?rx' = "rai_real ?x"
      let ?ry' = "rai_real ?y"
      let ?rx = "the_unique_root (p1,l1,r1)"
      let ?ry = "the_unique_root (p2,l2,r2)"
      have id: "?rx' = ?rx" "?ry' = ?ry" "rai_real x = ?rx" "rai_real y = ?ry" 
        unfolding x' y' rai_real_def by auto
      note rcx = rai_condD[OF x[unfolded x'], unfolded id]
      note rcy = rai_condD[OF y[unfolded y'], unfolded id]
      from rcx(1)[unfolded root_cond_def] have bndx: "of_rat l1 \<le> ?rx" "?rx \<le> of_rat r1"
        and rtx: "rpoly p1 ?rx = 0" by auto
      note n12 = root_info_condD(2)[OF rcx(9), of r1]
          root_info_condD(2)[OF rcy(9), of r2]
      show ?thesis
      proof (intro conjI impI)
        let ?set = "\<lambda> r. {x. x \<le> real_of_rat r \<and> rpoly p1 x = 0}"
        assume "?ri x = ?ri y"       
        hence p: "p2 = p1" and card: "card (?set r1) = card (?set r2)" using rx ry n12 by auto
        show "rai_real x = rai_real y" unfolding id using p root_index_unique_inv[OF card rcx(5,1,7) rcy(1,7)[unfolded p]]
          by simp
      next
        assume eq: "rai_real x = rai_real y"
        from rtx rcx(10)
        have algx: "alg_poly ?rx p1 \<and> irreducible p1 \<and> monic p1" unfolding alg_poly_def by (auto simp: poly_cond_def)
        from rcy(1)[unfolded root_cond_def] have bndy: "of_rat l2 \<le> ?ry" "?ry \<le> of_rat r2"
          and rty: "rpoly p2 ?ry = 0" by auto
        from rty rcy(10)
        have algy: "alg_poly ?ry p2 \<and> irreducible p2 \<and> monic p2" unfolding alg_poly_def by (auto simp: poly_cond_def)
        from algx have "algebraic ?rx" unfolding algebraic_altdef_rpoly by auto
        note unique = alg_poly_irreducible_unique[OF this]
        from eq have same: "?rx = ?ry" unfolding id by simp
        def xx \<equiv> "?rx"
        from rcx(1)[unfolded root_cond_def] have bndx: "of_rat l1 \<le> ?rx" "?rx \<le> of_rat r1"
          and rtx: "rpoly p1 ?rx = 0" by auto
        have p: "p1 = p2" using unique algx algy[folded same] by blast
        from p n12        
          rcx(1,7) rcy(1,7) same root_index_unique[of p1 l1 r1 ?rx l2 r2]
        have "(p1, ?n1 r1) = (p2, ?n2 r2)" by simp
        thus "?ri x = ?ri y" unfolding rx ry by simp
      qed
    qed
  qed note main = this
  {
    assume "info_fun_rai x = info_fun_rai y"
    thus "rai_real x = rai_real y" using main by blast
  }
  {
    assume 
      "rai_real x = rai_real y" 
    thus "info_fun_rai x = info_fun_rai y" using main by blast
  }
qed

lemma info_rai_fun: "real_of_rai x = real_of_rai y
  \<Longrightarrow> info_rai x = info_rai y"
  by (transfer, rule rai_info_fun(2), auto)

lemma info_rai_inj: "info_rai x = info_rai y \<Longrightarrow> real_of_rai x = real_of_rai y"
  by (transfer, rule rai_info_fun(1), auto)

lemma poly_rai_fun: "real_of_rai x = real_of_rai y
  \<Longrightarrow> poly_rai x = poly_rai y"
  using info_rai_fun[of x y] unfolding poly_rai_info_rai by auto

fun eq_fun_rai :: "rai_intern \<Rightarrow> rai_intern \<Rightarrow> bool" where
  "eq_fun_rai (Some (ri,p1,l1,r1)) (Some (_,p2,l2,r2)) = (l1 \<le> r2 \<and> l2 \<le> r1 \<and> p1 = p2 \<and>
    (let l = max l1 l2;
         r = min r1 r2
       in root_info.l_r ri l r \<noteq> 0))"
| "eq_fun_rai None None = True"
| "eq_fun_rai _ _ = False"

lemma eq_fun_rai: assumes rc: "rai_cond rai1" "rai_cond rai2"
  shows "(rai_real rai1 = rai_real rai2) = (eq_fun_rai rai1 rai2)" (is "?l = ?r")
proof (cases rai1)
  case (Some t1)
  then obtain ri1 p1 l1 r1 where rai1: "rai1 = Some (ri1,p1,l1,r1)" by (cases t1, auto)
  note ri1 = rai_condD[OF assms(1)[unfolded rai1]]
  show ?thesis
  proof (cases rai2)
    case None
    with ri1(3) show ?thesis by (simp add: rai1)
  next
    case (Some t2)
    then obtain ri2 p2 l2 r2 where rai2: "rai2 = Some (ri2,p2,l2,r2)" by (cases t2, auto)
    def l \<equiv> "max l1 l2"
    def r \<equiv> "min r1 r2"
    note ri2 = rai_condD[OF assms(2)[unfolded rai2]]
    have r: "?r = (l1 \<le> r2 \<and> l2 \<le> r1 \<and> p1 = p2 \<and> root_info.l_r ri1 l r \<noteq> 0)"
      unfolding l_def r_def rai1 rai2 by simp
    let ?x1 = "the_unique_root (p1,l1,r1)" let ?x2 = "the_unique_root (p2,l2,r2)"
    have l: "?l = (?x1 = ?x2)" unfolding rai1 rai2 by (simp add: rai_real_def)
    let ?R = real_of_rat
    note un1 = the_unique_root[OF ri1(7)]
    note un2 = the_unique_root[OF ri2(7)]
    from poly_cond_D[OF ri1(10)] have mon: "monic p1" by auto
    show "?l = ?r"
    proof (cases "l1 \<le> r2 \<and> l2 \<le> r1 \<and> p1 = p2")
      case False
      hence r: "?r = False" unfolding r by auto
      from False have choice: "?R l1 > ?R r2 \<or> ?R l2 > ?R r1 \<or> p1 \<noteq> p2" unfolding of_rat_less by auto
      from un1 have 1: "?R l1 \<le> ?x1" "?x1 \<le> ?R r1" by blast+
      from un2 have 2: "?R l2 \<le> ?x2" "?x2 \<le> ?R r2" by blast+
      from 1 2 choice have "?x1 \<noteq> ?x2 \<or> p1 \<noteq> p2" by auto
      hence l: "?l = False" 
      proof
        assume "?x1 \<noteq> ?x2" 
        thus ?thesis unfolding l by simp
      next
        assume "p1 \<noteq> p2" 
        hence "info_fun_rai rai1 \<noteq> info_fun_rai rai2" 
          unfolding rai1 rai2 by (simp add: info_fun_rai_def)
        with rai_info_fun[OF rc] have "rai_real rai1 \<noteq> rai_real rai2" by auto
        thus ?thesis by auto
      qed
      show ?thesis unfolding l r by auto
    next
      case True
      with order_trans[OF un1(1-2)] order_trans[OF un2(1-2)] have "l1 \<le> r1" "l2 \<le> r2" and p12: "p1 = p2" 
        unfolding of_rat_less_eq by auto
      with True have "l \<le> r" using ri1(7) unfolding l_def r_def by auto
      from root_info_condD(1)[OF ri1(9) this] True
      have r: "?r = (card {x. root_cond (p1, l, r) x} \<noteq> 0)" unfolding r by auto
      also have "\<dots> = ({x. root_cond (p1, l, r) x} \<noteq> {})"
        by (subst card_0_eq, unfold root_cond_def[abs_def] split, 
          rule finite_subset[OF _ finite_rpoly_roots[OF ri1(5)]], auto)
      also have "\<dots> = (\<exists> x. ?R l \<le> x \<and> x \<le> ?R r \<and> rpoly p1 x = 0)" unfolding root_cond_def by auto
      finally have r: "?r = (\<exists> x. ?R l \<le> x \<and> x \<le> ?R r \<and> rpoly p1 x = 0)" .
      show ?thesis
      proof (cases "?x1 = ?x2")
        case True
        have ?r unfolding r
        proof (intro exI[of _ ?x2] conjI)
          show "?R l \<le> ?x2" "?x2 \<le> ?R r" using  un2(1-2) un1(1-2)[unfolded True]
            unfolding l_def r_def by auto
          show "rpoly p1 (the_unique_root (p2, l2, r2)) = 0" 
            unfolding p12 by (rule un2(3))
        qed
        thus ?thesis using True l by blast
      next
        case False
        hence l: "?l = False" unfolding l by simp
        have "\<not> ?r"
        proof 
          assume ?r
          from this[unfolded r] obtain x where 
            lx: "?R l \<le> x" and xr: "x \<le> ?R r" and p1: "rpoly p1 x = 0" by auto
          with p12 have p2: "rpoly p2 x = 0" by auto
          have max: "?R (max l1 l2) = max (?R l1) (?R l2)" by (simp add: max_def of_rat_less_eq)
          have min: "?R (min r1 r2) = min (?R r1) (?R r2)" by (simp add: min_def of_rat_less_eq)
          from lx xr have x1: "?R l1 \<le> x" "x \<le> ?R r1" and x2: "?R l2 \<le> x" "x \<le> ?R r2" 
            unfolding l_def r_def max min by auto
          from p1 x1 have x1: "root_cond (p1,l1,r1) x" by (simp add: root_cond_def)
          from p2 x2 have x2: "root_cond (p2,l2,r2) x" by (simp add: root_cond_def)
          from un1(5)[OF x1] un2(5)[OF x2] have "?x1 = ?x2" by simp
          with False show False ..
        qed
        thus ?thesis unfolding l by simp
      qed
    qed
  qed
next
  case None note rai1 = this
  show ?thesis
  proof (cases rai2)
    case (Some t2)
    then obtain ri2 p2 l2 r2 where rai2: "rai2 = Some (ri2,p2,l2,r2)" by (cases t2, auto)
    note ri2 = rai_condD[OF assms(2)[unfolded rai2]]
    from rai1 rai2 ri2(3) show ?thesis by simp
  qed (simp add: rai1)
qed

declare eq_fun_rai.simps[simp del]
      
lift_definition eq_rai :: "real_alg_intern \<Rightarrow> real_alg_intern \<Rightarrow> bool" is eq_fun_rai .

lemma eq_rai: "(real_of_rai x = real_of_rai y) = (eq_rai x y)"
  by (transfer, insert eq_fun_rai, auto)

context
begin

context
  fixes cr1 cr2 :: "rat \<Rightarrow> rat \<Rightarrow> nat"
begin
partial_function (tailrec) compare_rai_intern_main :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> order" where
  [code]: "compare_rai_intern_main l1 r1 l2 r2 = (if r1 < l2 then Lt else if r2 < l1 then Gt 
    else let 
      (l1',r1') = tighten_poly_bounds cr1 l1 r1;
      (l2',r2') = tighten_poly_bounds cr2 l2 r2
    in compare_rai_intern_main l1' r1' l2' r2')
    "

lemma compare_rai_intern_main: assumes ri1: "root_info_cond ri1 p1"
  and cr1: "cr1 = root_info.l_r ri1"
  and ri2: "root_info_cond ri2 p2"
  and cr2: "cr2 = root_info.l_r ri2"  
  and ur1: "unique_root (p1,l1,r1)"
  and ur2: "unique_root (p2,l2,r2)"
  and diff: "the_unique_root (p1,l1,r1) \<noteq> the_unique_root (p2,l2,r2)"
 shows "compare_rai_intern_main l1 r1 l2 r2 = compare (the_unique_root (p1,l1,r1)) (the_unique_root (p2,l2,r2))"
proof -
  let ?r = real_of_rat
  {
    fix d x y
    assume d: "d = (r1 - l1) + (r2 - l2)" and xy: "x = the_unique_root (p1,l1,r1)" "y = the_unique_root (p2,l2,r2)"
    def delta \<equiv> "abs (x - y) / 4"
    have delta: "delta > 0" and diff: "x \<noteq> y" unfolding delta_def using diff xy by auto
    let ?rel' = "{(x, y). 0 \<le> y \<and> delta_gt delta x y}"
    let ?rel = "inv_image ?rel' ?r"
    have SN: "SN ?rel" by (rule SN_inv_image[OF delta_gt_SN[OF delta]])
    from d ur1 ur2
    have ?thesis unfolding xy[symmetric] using xy
    proof (induct d arbitrary: l1 r1 l2 r2 rule: SN_induct[OF SN])
      case (1 d l1 r1 l2 r2)
      note IH = 1(1)
      note d = 1(2)
      note ur = 1(3-4)
      note xy = 1(5-6)
      note simps = compare_rai_intern_main.simps[of l1 r1 l2 r2]
      note urx = the_unique_root[OF ur(1), folded xy]
      note ury = the_unique_root[OF ur(2), folded xy]
      show ?case (is "?l = _")
      proof (cases "r1 < l2")
        case True
        hence l: "?l = Lt" and lt: "?r r1 < ?r l2" unfolding simps of_rat_less by auto
        show ?thesis unfolding l using lt True urx(2) ury(1) 
          by (auto simp: compare_real_def comparator_of_def)
      next
        case False note le = this
        show ?thesis
        proof (cases "r2 < l1")
          case True
          with le have l: "?l = Gt" and lt: "?r r2 < ?r l1" unfolding simps of_rat_less by auto
          show ?thesis unfolding l using lt True ury(2) urx(1) 
            by (auto simp: compare_real_def comparator_of_def)
        next
          case False
          obtain l1' r1' where tb1: "tighten_poly_bounds cr1 l1 r1 = (l1',r1')" by force
          obtain l2' r2' where tb2: "tighten_poly_bounds cr2 l2 r2 = (l2',r2')" by force
          from False le tb1 tb2 have l: "?l = compare_rai_intern_main l1' r1' l2' r2'" unfolding simps 
            by auto
          from tighten_poly_bounds[OF tb1 ur(1) ri1 cr1]
          have rc1: "root_cond (p1, l1', r1') (the_unique_root (p1, l1, r1))" 
            and bnd1: "l1 \<le> l1'" "l1' \<le> r1'" "r1' \<le> r1" and d1: "r1' - l1' = (r1 - l1) / 2" by auto
          from unique_root_sub_interval[OF ur(1) rc1 bnd1(1,3)] xy
          have ur1: "unique_root (p1, l1', r1')" and x: "x = the_unique_root (p1, l1', r1')" by auto
          from tighten_poly_bounds[OF tb2 ur(2) ri2 cr2]
          have rc2: "root_cond (p2, l2', r2') (the_unique_root (p2, l2, r2))" 
            and bnd2: "l2 \<le> l2'" "l2' \<le> r2'" "r2' \<le> r2" and d2: "r2' - l2' = (r2 - l2) / 2" by auto
          from unique_root_sub_interval[OF ur(2) rc2 bnd2(1,3)] xy
          have ur2: "unique_root (p2, l2', r2')" and y: "y = the_unique_root (p2, l2', r2')" by auto
          def d' \<equiv> "d/2"
          have d': "d' = r1' - l1' + (r2' - l2')" unfolding d'_def d d1 d2 by (simp add: field_simps)
          have d'0: "d' \<ge> 0" using bnd1 bnd2 unfolding d' by auto
          have dd: "d - d' = d/2" unfolding d'_def by simp
          have "abs (x - y) \<le> 2 * ?r d"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            hence lt: "2 * ?r d < abs (x - y)" by auto
            have "r1 - l1 \<le> d" "r2 - l2 \<le> d" unfolding d using bnd1 bnd2 by auto
            from this[folded of_rat_less_eq[where 'a = real]] lt 
            have "?r (r1 - l1) < abs (x - y) / 2" "?r (r2 - l2) < abs (x - y) / 2" 
              and dd: "?r r1 - ?r l1 \<le> ?r d" "?r r2 - ?r l2 \<le> ?r d" by (auto simp: of_rat_diff)
            from le have "r1 \<ge> l2" by auto hence r1l2: "?r r1 \<ge> ?r l2" unfolding of_rat_less_eq by auto
            from False have "r2 \<ge> l1" by auto hence r2l1: "?r r2 \<ge> ?r l1" unfolding of_rat_less_eq by auto            
            show False
            proof (cases "x \<le> y")
              case True
              from urx(1-2) dd(1) have "?r r1 \<le> x + ?r d" by auto 
              with r1l2 have "?r l2 \<le> x + ?r d" by auto
              with True lt ury(2) dd(2) show False by auto
            next
              case False
              from ury(1-2) dd(2) have "?r r2 \<le> y + ?r d" by auto 
              with r2l1 have "?r l1 \<le> y + ?r d" by auto
              with False lt urx(2) dd(1) show False by auto
            qed              
          qed
          hence dd': "delta_gt delta (?r d) (?r d')" unfolding delta_gt_def of_rat_diff[symmetric] delta_def dd by auto
          show ?thesis unfolding l
            by (rule IH[OF _ d' ur1 ur2 x y], insert d'0 dd', auto)
        qed
      qed
    qed
  }            
  thus ?thesis by auto
qed
end

private fun compare_rai_intern :: "rai_intern \<Rightarrow> rai_intern \<Rightarrow> order" where
  "compare_rai_intern (Some x) (Some y) = (if eq_fun_rai (Some x) (Some y) then Eq 
    else (case x of (ri,p,l,r) \<Rightarrow> (case y of (ri',p',l',r')
      \<Rightarrow> compare_rai_intern_main (root_info.l_r ri) (root_info.l_r ri') l r l' r')))"
| "compare_rai_intern (Some (ri,p,l,r)) None = (if sgn r = 1 then Gt else Lt)"
| "compare_rai_intern None (Some (ri,p,l,r)) = (if sgn r = 1 then Lt else Gt)"
| "compare_rai_intern None None = Eq"

private lemma compare_rai_intern: assumes rc1: "rai_cond x1" and rc2: "rai_cond x2"
shows "compare_rai_intern x1 x2 = compare (rai_real x1) (rai_real x2)" (is "?l = ?r")
proof (cases x1)
  case None note x1 = this
  show ?thesis
  proof (cases x2)
    case None
    with x1 show ?thesis by simp
  next
    case (Some xt2) note x2 = this
    obtain ri2 p2 l2 r2 where xt2: "xt2 = (ri2,p2,l2,r2)" by (cases xt2, auto)
    note rc2 = rai_condD[OF rc2[unfolded x2 xt2]]
    from rc2(4,6) None have id: "rai_real x1 = 0" "sgn (rai_real x2) = of_rat (sgn r2)" "sgn r2 \<noteq> 0" unfolding x2 xt2 by auto
    from None x2 xt2 have l: "?l = (if sgn r2 = 1 then Lt else Gt)" by simp
    show ?thesis unfolding l using id by (auto simp: compare_real_def comparator_of_def sgn_real_def split: if_splits)
  qed
next
  case (Some xt1) note x1 = this
  obtain ri1 p1 l1 r1 where xt1: "xt1 = (ri1,p1,l1,r1)" by (cases xt1, auto)
  note rc1 = rai_condD[OF rc1[unfolded x1 xt1]]
  show ?thesis
  proof (cases x2)
    case None
    from rc1(4,6) None have id: "rai_real x2 = 0" "sgn (rai_real x1) = of_rat (sgn r1)" "sgn r1 \<noteq> 0" unfolding x1 xt1 by auto
    from None x1 xt1 have l: "?l = (if sgn r1 = 1 then Gt else Lt)" by simp
    show ?thesis unfolding l using id by (auto simp: compare_real_def comparator_of_def sgn_real_def split: if_splits)
  next
    case (Some xt2) note x2 = this
    show ?thesis
    proof (cases "eq_fun_rai x1 x2")
      case True
      with x1 x2 eq_fun_rai[OF assms] show ?thesis by simp
    next
      case False
      obtain ri2 p2 l2 r2 where xt2: "xt2 = (ri2,p2,l2,r2)" by (cases xt2, auto)
      let ?cri = "compare_rai_intern_main (root_info.l_r ri1) (root_info.l_r ri2) l1 r1 l2 r2"
      note rc2 = rai_condD[OF rc2[unfolded x2 xt2]]
      from False xt1 xt2 x1 x2 have "?l = ?cri" by simp 
      also have "\<dots> = ?r" 
        by (subst compare_rai_intern_main[OF rc1(9) refl rc2(9) refl rc1(7) rc2(7)],
        insert eq_fun_rai[OF assms] x1 x2 xt1 xt2 False, auto simp: rai_real_def)
      finally show ?thesis .
    qed
  qed
qed

lift_definition compare_rai :: "real_alg_intern \<Rightarrow> real_alg_intern \<Rightarrow> order" is compare_rai_intern .

lemma compare_rai: "compare_rai x1 x2 = compare (real_of_rai x1) (real_of_rai x2)"
  by (transfer, rule compare_rai_intern, auto)

lift_definition eq_rat_rai :: "rat \<Rightarrow> real_alg_intern \<Rightarrow> bool" is
  "\<lambda> x y. case y of None \<Rightarrow> x = 0 | Some (ri,p,l,r) \<Rightarrow> l \<le> x \<and> x \<le> r \<and> poly p x = 0" .

lemma eq_rat_rai: "eq_rat_rai x y = (of_rat x = real_of_rai y)"
proof (transfer)
  fix x y
  assume y: "y \<in> Collect rai_cond"
  show "(case y of None \<Rightarrow> x = 0 | Some ( ri, p, l, r) \<Rightarrow> l \<le> x \<and> x \<le> r \<and> poly p x = 0) =
           (real_of_rat x = rai_real y)" (is "?l = ?r")
  proof (cases y)
    case (Some tup)
    then obtain ri p l r where id: "y = Some ( ri, p, l, r)" by (cases tup, auto)
    from y[unfolded id] have "rai_cond (Some ( ri, p, l, r))" by auto
    note ri = rai_condD[OF this]
    note un = the_unique_root[OF ri(7)]
    have l: "?l = (l \<le> x \<and> x \<le> r \<and> poly p x = 0)" unfolding id by auto
    have r: "?r = (of_rat x = the_unique_root (p,l,r))" unfolding id by (simp add: rai_real_def)
    show ?thesis
    proof
      assume ?r
      from un(1-3)[folded this[unfolded r], unfolded of_rat_less_eq] show ?l unfolding l
        by (simp add: eval_poly_def)
    next
      let ?R = real_of_rat
      assume ?l
      from this[unfolded l] have "?R l \<le> ?R x" "?R x \<le> ?R r" "rpoly p (?R x) = 0"
        unfolding of_rat_less_eq by (auto simp: eval_poly_def)
      hence "root_cond (p,l,r) (?R x)" by (simp add: root_cond_def)
      from un(5)[OF this] show ?r unfolding r by simp
    qed
  qed simp
qed 

lift_definition compare_rat_rai :: "rat \<Rightarrow> real_alg_intern \<Rightarrow> order" is
  "\<lambda> x y. case y of None \<Rightarrow> compare x 0 | Some (ri,p,l,r) \<Rightarrow>
    case tighten_poly_bounds_for_x (root_info.l_r ri) x l r of (l',r') \<Rightarrow> compare x l'" .

lemma compare_rat_rai: "of_rat x \<noteq> real_of_rai y \<Longrightarrow> compare_rat_rai x y = compare (of_rat x) (real_of_rai y)"
proof (transfer)
  fix x y
  let ?r = "real_of_rat"
  let ?x = "?r x"
  assume "y \<in> Collect rai_cond" and diff: "?x \<noteq> rai_real y"
  hence rc: "rai_cond y" by auto
  show "(case y of None \<Rightarrow> compare x 0 | Some ( ri, p, l, r) \<Rightarrow>
            case tighten_poly_bounds_for_x (root_info.l_r ri) x l r of
            (l', r') \<Rightarrow> compare x l') = compare (real_of_rat x) (rai_real y)" (is "?l = _")
  proof (cases y)
    case None
    thus ?thesis by (auto simp: compare_rat_def compare_real_def comparator_of_def)
  next
    case (Some yt) note y = this
    obtain ri p l r where yt: "yt = (ri,p,l,r)" by (cases yt, auto)
    note rc = rai_condD[OF rc[unfolded y yt]]
    obtain l' r' where tb: "tighten_poly_bounds_for_x (root_info.l_r ri) x l r = (l',r')" by force
    have l: "?l = compare x l'" unfolding y yt using tb by auto
    from yt y have id: "rai_real y = the_unique_root (p,l,r)" unfolding rai_real_def by simp    
    {
      assume "l \<le> x" "x \<le> r" 
      hence bnd: "?r l \<le> ?x" "?x \<le> ?r r" unfolding of_rat_less_eq by auto
      have "poly p x \<noteq> 0"
      proof
        assume "poly p x = 0"
        hence "rpoly p ?x = 0" unfolding rpoly.eval_poly_poly by simp
        with bnd have "root_cond (p,l,r) ?x" unfolding root_cond_def by auto
        from rc(8)[OF this] diff show False unfolding y yt by (simp add: rai_real_def)
      qed
    }
    from tighten_poly_bounds_for_x[OF rc(7) this id rc(9) refl tb]
    have rc: "root_cond (p,l',r') (rai_real y)" and diff: "\<not> (l' \<le> x \<and> x \<le> r')" by auto
    from diff have diff: "\<not> (?r l' \<le> ?x \<and> ?x \<le> ?r r')" "x < l' \<longleftrightarrow> ?x < ?r l'" unfolding of_rat_less_eq of_rat_less by auto
    from rc[unfolded root_cond_def split] have bnd: "?r l' \<le> rai_real y" "rai_real y \<le> ?r r'" by auto
    show ?thesis unfolding l using diff bnd
      by (auto simp: compare_real_def compare_rat_def comparator_of_def)
  qed
qed

end


lemma rai_info_poly: assumes "info_rai x = (p,n)"
  shows "monic p \<and> poly_cond p \<and> rpoly p (real_of_rai x) = 0 \<and> degree p \<ge> 1"
  using assms
proof (transfer)
  fix mode rai p n
  assume "rai \<in> Collect rai_cond" and rif: "info_fun_rai rai = (p, n)"
  hence rc: "rai_cond rai" by auto
  show "monic p \<and> poly_cond p \<and> rpoly p (rai_real rai) = 0 \<and> degree p \<ge> 1"
  proof (cases rai)
    case None
    hence p: "p = poly_rat 0" using rif by (simp add: info_fun_rai_def)
    show "monic p \<and> poly_cond p \<and> rpoly p (rai_real rai) = 0 \<and> degree p \<ge> 1" 
      using None unfolding p 
      by (metis Missing_Polynomial.irreducibleD(1) alg_polyD(2) alg_poly_of_rat coeff_0_degree_minus_1 
          diff_is_0_eq irr_monic_root_free_poly_rat(1) irr_monic_root_free_poly_rat(2) 
          le_cases le_degree le_zero_eq poly_cond_I rai_real_None rpoly.hom_zero)
  next
    case (Some tup)
    obtain ri q l r where "tup = ( ri, q, l, r)" by (cases tup, auto)
    with Some rif have tup: "tup = ( ri, p, l, r)" by (auto simp: info_fun_rai_def) 
    from rai_condD(1,5,10)[OF rc[unfolded Some tup]]
    have pc: "poly_cond p" and rt: "rpoly p (rai_real rai) = 0" and "p \<noteq> 0"
      unfolding root_cond_def Some tup by (auto simp: poly_cond_def)
    from poly_cond_D[OF pc] pc rt 
    show "monic p \<and> poly_cond p \<and> rpoly p (rai_real rai) = 0 \<and> degree p \<ge> 1"
      unfolding irreducible_def by auto
  qed
qed


(* ********************* *)
subsubsection\<open>Negation\<close>

definition uminus_rai_fun :: "rai_intern \<Rightarrow> rai_intern" where
  "uminus_rai_fun \<equiv> map_option (\<lambda> (ri,p,l,r) \<Rightarrow> let p' = monic_poly (poly_uminus p) in 
      ( count_roots_interval_rat p', p', -r, -l))"

lemma uminus_rai_main: assumes x: "rai_cond x"
  defines y: "y \<equiv> uminus_rai_fun x"
  shows "rai_cond y \<and> (rai_real y = - rai_real x)"
proof (cases x)
  case (Some plr)
  obtain ri p l r where plr: "plr = (ri,p,l,r)" by (cases plr, auto)
  from x Some plr have "rai_cond (Some (ri,p,l,r))" by auto
  note * = rai_condD[OF this]
  note inv = *(8)
  note un = *(10)
  note * = *(1-6)
  from Some plr have x: "x = Some (ri,p,l,r)" by simp
  let ?x = "rai_real (Some (ri,p,l,r))"
  let ?p = "poly_uminus p"
  let ?mp = "monic_poly ?p"
  let ?cr = "count_roots_interval_rat ?mp"
  from plr Some have y: "y = Some (?cr, ?mp, -r , -l)" 
    unfolding y uminus_rai_fun_def Let_def by auto
  {
    fix y
    assume "root_cond (?mp, - r, - l) y"
    hence mpy: "rpoly ?mp y = 0" and bnd: "- of_rat r \<le> y" "y \<le> - of_rat l"
      unfolding root_cond_def by (auto simp: of_rat_minus)
    from mpy have id: "rpoly p (- y) = 0" using rpoly_uminus[of p "-y"] 
      by (auto simp: monic_poly)
    from bnd have bnd: "of_rat l \<le> - y" "-y \<le> of_rat r" by auto
    from id bnd have "root_cond (p, l, r) (-y)" unfolding root_cond_def by auto
    from inv[OF this]
    have "- ?x = y" by simp
  } note inj = this
  have rc: "root_cond (?mp, - r, - l) (- ?x)"
    using *(1-6) unfolding root_cond_def y x 
    by (auto simp: of_rat_minus sgn_minus_rat monic_poly(1))
  have xp: "alg_poly ?x p" using *(1,5) unfolding root_cond_def split alg_poly_def by auto
  have mon: "monic ?mp" by (rule monic_poly(2), insert *, auto)
  from poly_uminus_irreducible poly_cond_D[OF un] *(5) 
  have mi: "irreducible ?mp" by (auto simp: monic_poly)
  from mi mon have un: "poly_cond ?mp" by (auto simp: poly_cond_def)
  from poly_cond_D[OF un] have sf: "square_free ?mp" by auto
  show ?thesis unfolding y x
    by (rule rai_cond_realI, insert * rc count_roots_interval_rat[OF sf], 
      auto simp: of_rat_minus sgn_minus_rat, insert inj un, auto simp: monic_poly(4))
qed (simp add: y uminus_rai_fun_def)

lift_definition uminus_rai :: "real_alg_intern \<Rightarrow> real_alg_intern" is uminus_rai_fun
  by (insert uminus_rai_main, auto)
  
lemma uminus_rai: "real_of_rai (uminus_rai x) = uminus (real_of_rai x)"
  by (transfer, insert uminus_rai_main, auto)

(* ********************* *)
subsubsection\<open>Inverse\<close>

definition "inverse_rai_fun \<equiv> map_option (\<lambda> (_,p,l,r) \<Rightarrow> let p' = monic_poly (poly_inverse p) in
    ( count_roots_interval_rat p', p', inverse r, inverse l))"

lemma inverse_rai_main: assumes x: "rai_cond x"
  defines y: "y \<equiv> inverse_rai_fun x"
  shows "rai_cond y \<and> (rai_real y = inverse (rai_real x))"
proof (cases x)
  case (Some plr)
  obtain ri p l r where plr: "plr = (ri,p,l,r)" by (cases plr, auto)
  from x Some plr have "rai_cond (Some (ri,p,l,r))" by auto
  note * = rai_condD[OF this]
  note un = *(10)
  note inv = *(8)
  note * = *(1-6)
  from Some plr have x: "x = Some (ri,p,l,r)" by simp
  let ?x = "rai_real (Some (ri,p,l,r))"
  from * have x0: "?x \<noteq> 0" by auto
  let ?p = "poly_inverse p"
  let ?mp = "monic_poly ?p"
  let ?cr = "count_roots_interval_rat ?mp"  
  from plr Some have y: "y = Some ( ?cr, ?mp, inverse r , inverse l)" 
    unfolding y Let_def inverse_rai_fun_def by auto
  have mon: "monic ?mp" by (rule monic_poly(2), insert *, auto)
  {
    fix y
    assume "root_cond (?mp, inverse r, inverse l) y"
    hence mpy: "rpoly ?mp y = 0" and bnd: "inverse (of_rat r) \<le> y" "y \<le> inverse (of_rat l)"
      unfolding root_cond_def by (auto simp: of_rat_inverse)
    from sgn_real_mono[OF bnd(1)] sgn_real_mono[OF bnd(2)] 
    have "sgn (of_rat r) \<le> sgn y" "sgn y \<le> sgn (of_rat l)"
      by (simp_all add: algebra_simps)
    with \<open>sgn l = sgn r\<close> \<open>sgn r \<noteq> 0\<close> have y0: "y \<noteq> 0" "inverse y \<noteq> 0" 
      and sgn: "sgn (inverse (of_rat r)) = sgn y" "sgn y = sgn (inverse (of_rat l))" 
      unfolding sgn_inverse inverse_sgn
      by (auto simp add: real_of_rat_sgn intro: order_antisym)
    from mpy have id: "rpoly p (inverse y) = 0" using y0(1) rpoly_inverse[OF y0(2), of p] 
      unfolding inverse_inverse_eq by (auto simp: monic_poly)
    from inverse_le_sgn[OF sgn(1) bnd(1)] inverse_le_sgn[OF sgn(2) bnd(2)]
    have bnd: "of_rat l \<le> inverse y" "inverse y \<le> of_rat r" by auto
    from id bnd have "root_cond (p,l,r) (inverse y)" unfolding root_cond_def by auto
    from inv[OF this] x0 have "inverse ?x = y" by auto
  } note inj = this
  have rc: "root_cond (?mp, inverse r, inverse l) (inverse ?x)"
    using * unfolding root_cond_def y x split
    by (auto simp: of_rat_inverse real_of_rat_sgn inverse_le_iff_sgn rpoly_inverse[OF x0] monic_poly)
  have xp: "alg_poly ?x p" using *(1,5) unfolding root_cond_def split alg_poly_def by auto
  from poly_inverse_irreducible[OF _ _ xp x0] poly_cond_D[OF un] *(5) monic_poly(1-3)
  have mi: "irreducible ?mp" and mon: "monic ?mp" by auto
  from poly_cond_D[OF un] have sf: "square_free p" by simp
  hence sf: "square_free ?mp" unfolding monic_poly
    by (rule poly_inverse_square_free)
  from mi mon have un: "poly_cond ?mp" by (auto simp: poly_cond_def)
  show ?thesis unfolding y x
    by (rule rai_cond_realI, insert * rc count_roots_interval_rat[OF sf], 
      auto simp: of_rat_inverse real_of_rat_sgn inverse_le_iff_sgn rpoly_inverse[OF x0]) 
    (insert inj un, auto simp: monic_poly)
qed (simp add: y inverse_rai_fun_def)

lift_definition inverse_rai :: "real_alg_intern \<Rightarrow> real_alg_intern" is inverse_rai_fun
  by (insert inverse_rai_main, auto)
  
lemma inverse_rai: "real_of_rai (inverse_rai x) = inverse (real_of_rai x)"
  by (transfer, insert inverse_rai_main, auto)

(* ********************* *)
subsubsection\<open>Floor\<close>

fun floor_rai_fun :: "rai_intern \<Rightarrow> int" where
  "floor_rai_fun None = 0"
| "floor_rai_fun (Some (ri,p,l,r)) = (let
    cr = root_info.l_r ri;
    (l',r') = tighten_poly_bounds_epsilon cr (1/2) l r;
    fr = floor r';
    fl = floor l';
    fr' = rat_of_int fr
    in (if fr = fl \<or> poly p fr' = 0 then fr else
    let (l'',r'') = tighten_poly_bounds_for_x cr fr' l' r'
    in if fr' < l'' then fr else fl))"

lemma floor_rai_fun: assumes "rai_cond x"
  shows "floor (rai_real x) = floor_rai_fun x"
proof (cases x)
  case None
  thus ?thesis by simp
next
  case (Some xt)
  obtain ri p l r where xt: "xt = (ri,p,l,r)" by (cases xt, auto)  
  obtain cr where cr: "cr = root_info.l_r ri" by auto
  obtain l' r' where tbe: "tighten_poly_bounds_epsilon cr (1 / 2) l r = (l',r')" by force
  let ?fr = "floor r'"
  let ?fl = "floor l'"
  let ?fr' = "rat_of_int ?fr"
  obtain l'' r'' where tbx: "tighten_poly_bounds_for_x cr ?fr' l' r' = (l'',r'')" by force
  note rc = assms[unfolded Some xt]
  note rcD = rai_condD[OF rc]
  have id: "floor_rai_fun x = ((if ?fr = ?fl \<or> poly p ?fr' = 0 then ?fr 
    else if ?fr' < l'' then ?fr else ?fl))"
    unfolding Some xt floor_rai_fun.simps tbe Let_def split tbx cr[symmetric] by simp
  let ?x = "rai_real x" 
  have x: "?x = the_unique_root (p,l,r)" unfolding Some xt by (simp add: rai_real_def)
  from tighten_poly_bounds_epsilon[OF rcD(7) refl rcD(9) cr tbe]
  have bnd: "l \<le> l'" "r' \<le> r" "r' - l' \<le> 1 / 2"
    and rc': "root_cond (p, l', r') (the_unique_root (p, l, r))" by auto
  let ?r = real_of_rat
  from rc'[folded x, unfolded root_cond_def split]
  have ineq: "?r l' \<le> ?x" "?x \<le> ?r r'" "?r l' \<le> ?r r'" by auto
  hence lr': "l' \<le> r'" unfolding of_rat_less_eq by simp
  have flr: "?fl \<le> ?fr"
    by (rule floor_mono[OF lr'])
  from rai_cond_sub_interval[OF rc rc' bnd(1,2)]
  have rc': "rai_cond (Some ( ri, p, l', r'))"
    and id': "rai_real (Some ( ri, p, l', r')) = rai_real (Some ( ri, p, l, r))" .
  have x: "?x = the_unique_root (p,l',r')"
    unfolding Some xt using id' by (simp add: rai_real_def)
  {
    assume "?fr \<noteq> ?fl"
    with flr have flr: "?fl \<le> ?fr - 1" by simp
    have "?fr' \<le> r'"  "l' \<le> ?fr'" using flr bnd by linarith+
  } note fl_diff = this
  show ?thesis
  proof (cases "?fr = ?fl \<or> poly p ?fr' = 0")
    case True
    hence id: "floor_rai_fun x = ?fr" unfolding id by auto
    show ?thesis unfolding id
    proof (cases "?fr = ?fl")
      case True
      hence id: "floor (?r l') = floor (?r r')" unfolding real_of_rat_floor by simp
      have "floor ?x \<le> floor (?r r')"
        by (rule floor_mono[OF ineq(2)])
      moreover have "floor (?r l') \<le> floor ?x"
        by (rule floor_mono[OF ineq(1)])
      ultimately have "floor ?x = floor (?r r')" unfolding id by simp
      thus "floor ?x = ?fr" unfolding real_of_rat_floor .
    next
      case False
      from True False have "poly p ?fr' = 0" by simp
      hence 0: "rpoly p (?r ?fr') = 0" unfolding rpoly.eval_poly_poly by simp
      have "root_cond (p,l',r') (?r ?fr')" unfolding root_cond_def split 0 of_rat_less_eq
        using fl_diff[OF False] by auto
      from rai_condD(8)[OF rc' this]  
      have "floor ?x = ?r ?fr'" unfolding x by (simp add: rai_real_def)
      thus "floor ?x = ?fr" by simp
    qed
  next
    case False
    with id have id: "floor_rai_fun x = (if ?fr' < l'' then ?fr else ?fl)" by simp
    from False have 0: "l' \<le> ?fr' \<Longrightarrow> ?fr' \<le> r' \<Longrightarrow> poly p ?fr' \<noteq> 0" by auto
    note rcD = rai_condD[OF rc']
    from tighten_poly_bounds_for_x[OF rcD(7) 0 x rcD(9) cr tbx]
    have ineq': "l' \<le> l''" "r'' \<le> r'" and lr'': "l'' \<le> r''" and rc'': "root_cond (p,l'',r'') ?x"
      and fr': "\<not> (l'' \<le> ?fr' \<and> ?fr' \<le> r'')" by auto
    from rc''[unfolded root_cond_def split]
    have ineq'': "?r l'' \<le> ?x" "?x \<le> ?r r''" by auto
    from False have "?fr \<noteq> ?fl" by auto
    note fr = fl_diff[OF this]
    show ?thesis
    proof (cases "?fr' < l''")
      case True
      with id have id: "floor_rai_fun x = ?fr" by simp 
      have "floor ?x \<le> ?fr" using floor_mono[OF ineq(2)] by simp      
      moreover 
      from True have "?r ?fr' < ?r l''" unfolding of_rat_less .
      with ineq''(1) have "?r ?fr' \<le> ?x" by simp
      from floor_mono[OF this]
      have "?fr \<le> floor ?x" by simp 
      ultimately show ?thesis unfolding id by auto
    next
      case False
      with id have id: "floor_rai_fun x = ?fl" by simp
      from False have "l'' \<le> ?fr'" by auto
      from floor_mono[OF ineq(1)] have "?fl \<le> floor ?x" by simp
      moreover have "floor ?x \<le> ?fl"
      proof -
        from False fr' have fr': "r'' < ?fr'" by auto
        hence "floor r'' < ?fr" by linarith
        with floor_mono[OF ineq''(2)] 
        have "floor ?x \<le> ?fr - 1" by auto
        also have "?fr - 1 = floor (r' - 1)" by simp
        also have "\<dots> \<le> ?fl"
          by (rule floor_mono, insert bnd, auto)
        finally show ?thesis .
      qed
      ultimately show ?thesis unfolding id by auto
    qed
  qed
qed

lift_definition floor_rai :: "real_alg_intern \<Rightarrow> int" is floor_rai_fun .

lemma floor_rai: "floor (real_of_rai x) = floor_rai x"
  by (transfer, insert floor_rai_fun, auto)

(* ********************* *)
subsubsection\<open>Root\<close>


definition rpoly_root_delta :: "rat poly \<Rightarrow> real" where
  "rpoly_root_delta p = Min (insert 1 { abs (x - y) | x y. rpoly p x = 0 \<and> rpoly p y = 0 \<and> x \<noteq> y}) / 4"

lemma rpoly_root_delta: assumes "p \<noteq> 0"
  shows "rpoly_root_delta p > 0"
    "2 \<le> card (Collect (root_cond (p, l, r))) \<Longrightarrow> rpoly_root_delta p \<le> real_of_rat (r - l) / 4"
proof -
  let ?z = "0 :: real"
  let ?R = "{x. rpoly p x = ?z}"
  let ?set = "{ abs (x - y) | x y. rpoly p x = ?z  \<and> rpoly p y = 0 \<and> x \<noteq> y}"
  def S \<equiv> "insert 1 ?set"
  from finite_rpoly_roots[OF assms] have finR: "finite ?R" and fin: "finite (?R \<times> ?R)" by auto
  have "finite ?set"
    by (rule finite_subset[OF _ finite_imageI[OF fin, of "\<lambda> (x,y). abs (x - y)"]], force)
  hence fin: "finite S" and ne: "S \<noteq> {}" and pos: "\<And> x. x \<in> S \<Longrightarrow> x > 0" unfolding S_def by auto
  have delta: "rpoly_root_delta p = Min S / 4" unfolding rpoly_root_delta_def S_def ..
  have pos: "Min S > 0" using fin ne pos by auto
  show "rpoly_root_delta p > 0" unfolding delta using pos by auto
  let ?S = "Collect (root_cond (p, l, r))"
  assume "2 \<le> card ?S"
  hence 2: "Suc (Suc 0) \<le> card ?S" by simp
  have finS: "finite ?S"
    by (rule finite_subset[OF _ finR], auto simp: root_cond_def)
  from 2[unfolded card_le_Suc_iff[OF finS]] obtain x T where 
    ST: "?S = insert x T" and xT: "x \<notin> T" and 1: "Suc 0 \<le> card T" and finT: "finite T" by auto
  from 1[unfolded card_le_Suc_iff[OF finT]] obtain y where yT: "y \<in> T" by auto
  from ST xT yT have x: "x \<in> ?S" and y: "y \<in> ?S" and xy: "x \<noteq> y" by auto
  hence "abs (x - y) \<in> S" unfolding S_def root_cond_def[abs_def] by auto
  with fin have "Min S \<le> abs (x - y)" by auto
  with pos have le: "Min S / 2 \<le> abs (x - y) / 2" by auto
  from x y have "abs (x - y) \<le> of_rat r - of_rat l" unfolding root_cond_def[abs_def] by auto
  also have "\<dots> = of_rat (r - l)" by (auto simp: of_rat_diff)
  finally have "abs (x - y) / 2 \<le> of_rat (r - l) / 2" by auto
  with le show "rpoly_root_delta p \<le> real_of_rat (r - l) / 4" unfolding delta by auto
qed

definition sgn_rai_rat :: "rai_intern \<Rightarrow> rat" where
  "sgn_rai_rat impl = (case impl of None \<Rightarrow> 0 | Some (ri,p,l,r) \<Rightarrow> sgn r)"

lemma sgn_less_eq_1_rat: fixes a b :: rat
  shows "sgn a = 1 \<Longrightarrow> a \<le> b \<Longrightarrow> sgn b = 1" 
  by (metis (no_types, hide_lams) not_less one_neq_neg_one one_neq_zero order_trans sgn_rat_def)

lemma sgn_less_eq_1_real: fixes a b :: real
  shows "sgn a = 1 \<Longrightarrow> a \<le> b \<Longrightarrow> sgn b = 1" 
  by (metis (no_types, hide_lams) not_less one_neq_neg_one one_neq_zero order_trans sgn_real_def)

lemma card_1_Collect_ex1: assumes "card (Collect P) = 1"
  shows "\<exists>! x. P x"
proof -
  from assms[unfolded card_eq_1_iff] obtain x where "Collect P = {x}" by auto
  thus ?thesis
    by (intro ex1I[of _ x], auto)
qed

context
  fixes n :: nat
begin
private definition initial_lower_bound :: "rat \<Rightarrow> rat" where 
  "initial_lower_bound l = (if l \<le> 1 then l else of_int (root_rat_floor n l))"

private definition initial_upper_bound :: "rat \<Rightarrow> rat" where
  "initial_upper_bound r = (of_int (root_rat_ceiling n r))"

context
  fixes p' p :: "rat poly"
  and ri' :: "root_info"
  and cr' cr :: "rat \<Rightarrow> rat \<Rightarrow> nat"
begin  
partial_function (tailrec) tighten_bound_root :: 
  "rat \<times> rat \<Rightarrow> rat \<times> rat \<Rightarrow> rai_intern_flat" where
  [code]: "tighten_bound_root rbnd pbnd = (case (rbnd,pbnd) of ((l',r'), (l,r))
    \<Rightarrow> 
    if cr' l' r' = 1 then (ri',p',l',r') else let
      m' = (l' + r') / 2;
      m = m' ^ n
      in if l \<le> m \<and> m \<le> r \<and> poly p m = 0 then (poly_rat_root_info m', poly_rat m',m',m')
      else (case tighten_poly_bounds_for_x cr m l r of (L,R) \<Rightarrow> 
        if m < L then tighten_bound_root (m',r') (L,R) 
      else tighten_bound_root (l',m') (L,R)))"


lemma tighten_bound_root: assumes n: "n \<noteq> 0"
  and ur: "unique_root (p,l,r)"
  and rt: "root_cond (p',l',r') x"
  and u: "u = the_unique_root (p,l,r)"
  and x: "x = root n u"
  and cr: "root_info_cond ri p" "cr = root_info.l_r ri"
  and cr': "root_info_cond ri' p'" "cr' = root_info.l_r ri'"
  and res: "tighten_bound_root (l',r') (l,r) = (Ri,P,L,R)"
  and p: "p \<noteq> 0" 
  and p': "p' \<noteq> 0"
  and sgn: "sgn l = 1" "sgn l' = 1"
  shows "unique_root (P,L,R)" "root_cond (P,L,R) x" "P \<noteq> 0" "sgn L = 1" "sgn R = 1" "sgn x = 1"
    "root_info_cond Ri P"
proof -
  def delta \<equiv> "rpoly_root_delta p'"
  have delta: "delta > 0" unfolding delta_def by (rule rpoly_root_delta[OF p'])
  let ?P = "\<lambda> ((l',r'), (l,r)) . unique_root (p,l,r) \<longrightarrow> root_cond (p',l',r') x \<longrightarrow>
    u = the_unique_root (p,l,r) \<longrightarrow> tighten_bound_root (l',r') (l,r) = (Ri,P,L,R) \<longrightarrow> sgn l = 1 \<longrightarrow>
    sgn l' = 1 \<longrightarrow> 
    (unique_root (P,L,R) \<and> root_cond (P,L,R) x \<and> P \<noteq> 0 \<and> sgn L = 1 \<and> root_info_cond Ri P)"
  let ?dist = "\<lambda> ((l',r'),(l,r)). real_of_rat (r' - l')"
  let ?rel' = "{(x, y). 0 \<le> y \<and> delta_gt delta x y}"
  let ?rel = "inv_image ?rel' ?dist"
  have SN: "SN ?rel" by (rule SN_inv_image[OF delta_gt_SN[OF delta]])
  have "?P ((l',r'),(l,r))"
  proof (induct rule: SN_induct[OF SN])
    case (1 input)
    obtain l' r' l r where input: "input = ((l',r'),(l,r))" by (cases input, auto)
    show ?case unfolding input split
    proof (intro impI)
      assume ur: "unique_root (p,l,r)"
        and rc': "root_cond (p',l',r') x"
        and u: "u = the_unique_root (p,l,r)"
        and res: "tighten_bound_root (l', r') (l, r) = ( Ri, P, L, R)"
        and sgn: "sgn l = 1" "sgn l' = 1"
      let ?l' = "real_of_rat l'"
      let ?r' = "real_of_rat r'"
      note rc'' = rc'[unfolded root_cond_def split] 
      from rc'' have "?l' \<le> ?r'" by auto
      hence lr': "l' \<le> r'" by (auto simp: of_rat_less_eq)
      note res = res[unfolded tighten_bound_root.simps[of "(l',r')"] split Let_def]
      show "unique_root (P,L,R) \<and> root_cond (P,L,R) x \<and> P \<noteq> 0 \<and> sgn L = 1 \<and> root_info_cond Ri P"
      proof (cases "cr' l' r' = 1")
        case True
        with res have id: "P = p'" "L = l'" "R = r'" "Ri = ri'" by auto
        from True[unfolded cr'(2) root_info_condD(1)[OF cr'(1) lr']]
        have "card (Collect (root_cond (p',l',r'))) = 1" .
        from card_1_Collect_ex1[OF this]
        have "unique_root (p',l',r')" unfolding unique_root_def .
        with rc' p' sgn cr' show ?thesis unfolding id by auto
      next
        case False note card = this
        hence "(cr' l' r' = 1) = False" by auto
        note res = res[unfolded this if_False]
        def m' \<equiv> "(l' + r') / 2"
        let ?m = "m' ^ n"
        let ?m' = "real_of_rat m'"
        have lm': "l' \<le> m'" and mr': "m' \<le> r'" using lr' m'_def by auto
        from sgn_less_eq_1_rat[OF sgn(2) lm'] have sgnm': "sgn m' = 1" .
        note res = res[folded m'_def]
        let ?cond = "root_cond (p,l,r) (of_rat ?m)"
        have cond: "(l \<le> ?m \<and> ?m \<le> r \<and> poly p ?m = 0) = ?cond"
          unfolding root_cond_def split of_rat_less_eq rpoly.eval_poly_poly by auto
        note res = res[unfolded cond]
        show ?thesis
        proof (cases ?cond)
          case True
          hence id: "P = poly_rat m'" "L = m'" "R = m'" "Ri = poly_rat_root_info m'" using card res by auto
          from the_unique_root(5)[OF ur True, folded u] have u: "u = (of_rat m') ^ n" unfolding of_rat_power .
          have xm: "x = of_rat m'" unfolding arg_cong[OF u, of "root n", folded x]
            by (rule real_root_pos2, insert sgnm' n, cases "m' = 0"; cases "m' < 0"; auto simp: sgn_rat_def)
          have rc: "root_cond (poly_rat m', m', m') x" unfolding root_cond_def split xm by simp
          show ?thesis unfolding id using rc by (auto simp: sgnm' unique_root_def root_cond_def)
        next
          case False note m_no_root = this
          hence "?cond = False" by auto
          note res = res[unfolded this if_False]
          let ?tight = "tighten_poly_bounds_for_x cr ?m l r"
          obtain LL RR where tight: "?tight = (LL,RR)" by force
          from m_no_root[folded cond] have "l \<le> ?m \<Longrightarrow> ?m \<le> r \<Longrightarrow> poly p ?m \<noteq> 0" by auto
          from tighten_poly_bounds_for_x[OF ur this u cr tight]
          have bnd: "l \<le> LL" "RR \<le> r" and rc': "root_cond (p,LL,RR) u" 
            and outside: "\<not> (LL \<le> ?m \<and> ?m \<le> RR)" by auto
          from sgn_less_eq_1_rat[OF sgn(1) bnd(1)] have sgnLL: "sgn LL = 1" .
          from unique_root_sub_interval[OF ur rc'[unfolded u] bnd, folded u]
          have ur': "unique_root (p, LL, RR)" and u': "u = the_unique_root (p, LL, RR)" by auto
          note IH = 1[unfolded input]
          note res = res[unfolded tight split]
          let ?d = "r' - l'"
          let ?d' = "real_of_rat ?d"
          let ?diff = "(r' - l') / 2" 
          let ?diff' = "real_of_rat ?diff"
          let ?in = "((l',r'),(l,r))"
          let ?recl = "((l',m'),(LL,RR))"
          let ?recr = "((m',r'),(LL,RR))"
          from lr' have size: "r' - m' = ?diff" "m' - l' = ?diff" 
            and bnd0: "?diff' \<ge> 0" unfolding m'_def
            by (auto simp: field_simps of_rat_less_eq)
          from lr' have d': "?d' \<ge> 0" unfolding zero_le_of_rat_iff by simp
          have "?d' - ?diff' = ?d' / 2" by (auto simp: field_simps of_rat_divide)
          also have "\<dots> \<ge> delta" 
          proof -
            let ?S = "Collect (root_cond (p',l',r'))"
            have fin: "finite ?S"
              by (rule finite_subset[OF _ finite_rpoly_roots[OF p']], auto simp: root_cond_def)
            from rc'' have "root_cond (p',l',r') x" unfolding root_cond_def by auto
            hence "x \<in> ?S" by auto
            with fin have "card ?S \<noteq> 0" by auto
            with card[unfolded cr'(2) root_info_condD(1)[OF cr'(1) lr']]
            have "card ?S \<ge> 2" by auto
            from rpoly_root_delta(2)[OF p' this]
            have "delta \<le> ?d' / 4" unfolding delta_def .
            also have "\<dots> \<le> ?d' / 2" using d' by simp
            finally show "delta \<le> ?d' / 2" .
          qed
          finally have rel: "(?d',?diff') \<in> ?rel'" using bnd0 unfolding delta_gt_def by auto
          have *: "(?d',?diff') = (?dist ?in, ?dist ?recl)"
               "(?d',?diff') = (?dist ?in, ?dist ?recr)"
            unfolding split size by auto
          from rel have "(?dist ?in, ?dist ?recl) \<in> ?rel'" "(?dist ?in, ?dist ?recr) \<in> ?rel'" 
            unfolding *[symmetric] by blast+
          hence rel: "(?in,?recl) \<in> ?rel" "(?in,?recr) \<in> ?rel" by auto
          have l0: "l > 0" using sgn(1) unfolding sgn_rat_def by (cases "l = 0"; cases "l < 0", auto)
          hence ll0: "real_of_rat l > 0" by auto
          have l'0: "l' > 0" using sgn(2) unfolding sgn_real_def by (cases "l' = 0"; cases "l' < 0", auto)
          hence ll'0: "real_of_rat l' > 0" by auto
          hence x0: "x > 0" using rc'' by linarith
          have u0: "u > 0" using the_unique_root(1)[OF ur, folded u] ll0 by linarith
          have uxn: "u = x^n" unfolding x 
            by (rule sym, rule real_root_pow_pos, insert n u0, auto)
          have rxn: "root n (x ^ n) = x"
            by (rule real_root_pos2, insert n x0, auto)
          have rm: "root n (of_rat ?m) = of_rat m'" unfolding of_rat_power
            by (rule real_root_pos2, insert n lm' ll'0, auto)
          show ?thesis 
          proof (cases "?m < LL")
            case True
            note outside = this
            with res have res: "tighten_bound_root (m', r') (LL, RR) = (Ri,P,L,R)" by auto
            have "of_rat ?m < real_of_rat LL" using outside of_rat_less by blast
            also have "\<dots> \<le> u" using the_unique_root(1)[OF ur', folded u'] by auto
            finally have "of_rat ?m < x ^ n" unfolding uxn .
            hence "root n (of_rat ?m) < root n (x ^ n)" 
              by (subst real_root_less_iff, insert n, auto)
            hence "?m' < x" unfolding rxn rm .
            with rc'' have rc: "root_cond (p', m', r') x" unfolding root_cond_def by auto
            note IH = IH[OF rel(2), unfolded split, rule_format, OF ur' rc u' res sgnLL sgnm']
            show ?thesis by (rule IH)
          next
            case False
            with res have res: "tighten_bound_root (l', m') (LL, RR) = (Ri,P,L,R)" by auto
            from False have "LL \<le> ?m" by auto
            with outside have outside: "RR < ?m" by auto
            have "x ^ n \<le> of_rat RR" 
              unfolding uxn[symmetric] using the_unique_root(2)[OF ur', folded u'] .
            also have "\<dots> < of_rat ?m" using outside of_rat_less by blast
            finally have "x ^ n < of_rat ?m" .
            hence "root n (x ^ n) < root n (of_rat ?m)" 
              by (subst real_root_less_iff, insert n, auto)
            hence "x < ?m'" unfolding rxn rm .
            with rc'' have rc: "root_cond (p', l', m') x" unfolding root_cond_def by auto
            note IH = IH[OF rel(1), unfolded split, rule_format, OF ur' rc u' res sgnLL sgn(2)]
            show ?thesis by (rule IH)
          qed
        qed
      qed
    qed
  qed
  from this[unfolded split, rule_format, OF ur rt u res sgn]
  show "unique_root (P,L,R)" "P \<noteq> 0" "root_info_cond Ri P" and rc: "root_cond (P,L,R) x" and sgn: "sgn L = 1" by auto
  from rc[unfolded root_cond_def split] have Lx: "of_rat L \<le> x" and LR: "of_rat L \<le> real_of_rat R" by auto
  from LR have "L \<le> R" by (auto simp: of_rat_less_eq)
  with sgn show "sgn R = 1" by (metis sgn_less_eq_1_rat)
  show "sgn x = 1" by (rule sgn_less_eq_1_real[OF _ Lx], insert sgn, simp add: real_of_rat_sgn)
qed

end

private definition root_rai_fun_pos :: "rai_intern \<Rightarrow> rai_intern" where
  "root_rai_fun_pos \<equiv> map_option (\<lambda> (ri,p,l,r) \<Rightarrow> 
  let p' = poly_nth_root n p; ri' = count_roots_interval_sf_rat p' in 
  rai_normalize_poly_flat 
    (tighten_bound_root p' p ri' (root_info.l_r ri') (root_info.l_r ri)
      (initial_lower_bound l, initial_upper_bound r) (l,r)))"

private definition "root_rai_fun impl \<equiv> if n = 0 then of_rat_rai_fun 0 else if sgn_rai_rat impl \<ge> 0 
    then root_rai_fun_pos impl
    else uminus_rai_fun (root_rai_fun_pos (uminus_rai_fun impl))"

context
  assumes n: "n \<noteq> 0"
begin  

lemma initial_upper_bound: assumes x: "x > 0" and xr: "x \<le> of_rat r"
  shows "sgn (initial_upper_bound r) = 1" "root n x \<le> of_rat (initial_upper_bound r)"
proof -
  have n: "n > 0" using n by auto
  note d = initial_upper_bound_def
  let ?r = "initial_upper_bound r"
  from x xr have r0: "r > 0" by (meson not_less of_rat_le_0_iff order_trans)
  hence "of_rat r > (0 :: real)" by auto
  hence "root n (of_rat r) > 0" using n by simp
  hence "1 \<le> ceiling (root n (of_rat r))" by auto
  hence "(1 :: rat) \<le> of_int (ceiling (root n (of_rat r)))" by linarith
  also have "\<dots> = ?r" unfolding d by simp
  finally show "sgn ?r = 1" unfolding sgn_rat_def by auto
  have "root n x \<le> root n (of_rat r)"
    unfolding real_root_le_iff[OF n] by (rule xr)
  also have "\<dots> \<le> of_rat ?r" unfolding d by simp
  finally show "root n x \<le> of_rat ?r" .
qed

lemma initial_lower_bound: assumes l: "l > 0" and lx: "of_rat l \<le> x"
  shows "sgn (initial_lower_bound l) = 1" "of_rat (initial_lower_bound l) \<le> root n x"
proof -
  have n: "n > 0" using n by auto
  note d = initial_lower_bound_def
  let ?l = "initial_lower_bound l"
  from l lx have x0: "x > 0" by (meson not_less of_rat_le_0_iff order_trans)
  have "sgn ?l = 1 \<and> of_rat ?l \<le> root n x"
  proof (cases "l \<le> 1")
    case True
    hence ll: "?l = l" and l0: "of_rat l \<ge> (0 :: real)" and l1: "of_rat l \<le> (1 :: real)" 
      using l unfolding True d by auto
    have sgn: "sgn ?l = 1" using l unfolding ll by auto
    have "of_rat ?l = of_rat l" unfolding ll by simp
    also have "of_rat l \<le> root n (of_rat l)" using real_root_increasing[OF _ _ l0 l1, of 1 n] n
      by (cases "n = 1", auto)
    also have "\<dots> \<le> root n x" using lx unfolding real_root_le_iff[OF n] .
    finally show ?thesis using sgn by auto
  next
    case False
    hence l: "(1 :: real) \<le> of_rat l" and ll: "?l = of_int (floor (root n (of_rat l)))" 
      unfolding d by auto
    hence "root n 1 \<le> root n (of_rat l)"
      unfolding real_root_le_iff[OF n] by auto
    hence "1 \<le> root n (of_rat l)" using n by auto
    from floor_mono[OF this] have "1 \<le> ?l"
      using one_le_floor unfolding ll by fastforce
    hence sgn: "sgn ?l = 1" by simp
    have "of_rat ?l \<le> root n (of_rat l)" unfolding ll by simp
    also have "\<dots> \<le> root n x" using lx unfolding real_root_le_iff[OF n] .
    finally have "of_rat ?l \<le> root n x" .
    with sgn show ?thesis by auto
  qed
  thus "sgn ?l = 1" "of_rat ?l \<le> root n x" by auto
qed

lemma root_rai_pos: assumes x: "rai_cond x" and nneg: "sgn_rai_rat x \<ge> 0" 
  defines y: "y \<equiv> root_rai_fun_pos x"
  shows "rai_cond y \<and> (rai_real y = root n (rai_real x))"
proof (cases x)
  case (Some plr)
  obtain ri p l r where plr: "plr = (ri,p,l,r)" by (cases plr, auto)
  let ?l = "initial_lower_bound l"
  let ?r = "initial_upper_bound r"
  from x Some plr have "rai_cond (Some (ri,p,l,r))" by auto
  note * = rai_condD[OF this]
  note inv = *(8)
  note ur = *(7)
  note cr = *(9)
  note * = *(1-6)
  note ** = *[unfolded root_cond_def]
  from Some plr have x: "x = Some (ri,p,l,r)" by simp
  let ?x = "rai_real (Some (ri,p,l,r))"
  from nneg[unfolded x sgn_rai_rat_def] have "sgn r \<ge> 0" by simp
  with * have "sgn r > 0" by linarith
  hence sgnl: "sgn l = 1" using * by auto
  from sgnl have l0: "l > 0" unfolding sgn_rat_def by (cases "l = 0"; cases "l < 0"; auto)
  hence ll0: "real_of_rat l > 0" by auto
  from ** have lx: "of_rat l \<le> ?x" by auto
  with ll0 have x0: "?x > 0" by linarith  
  note il = initial_lower_bound[OF l0 lx]
  from ** have "?x \<le> of_rat r" by auto
  note iu = initial_upper_bound[OF x0 this]
  let ?p = "poly_nth_root n p"
  let ?c = "count_roots_interval_sf_rat"
  let ?lr = "root_info.l_r"
  from x0 have id: "root n ?x ^ n = ?x" using n real_root_pow_pos by blast
  have rc: "root_cond (?p, ?l, ?r) (root n ?x)"
    unfolding root_cond_def using il iu ** by (auto simp: id rpoly_nth_root)
  from ** have p: "p \<noteq> 0" by auto
  hence p': "?p \<noteq> 0" using poly_nth_root_0[OF n, of p] by auto
  let ?tight = "tighten_bound_root ?p p (?c ?p) (?lr (?c ?p)) (?lr ri) (?l,?r) (l,r)"
  let ?norm = "rai_normalize_poly_flat  ?tight"
  from plr Some have y: "y = Some ?norm" 
    unfolding y root_rai_fun_pos_def Let_def by simp
  obtain un1 Cr P L R where tight: "?tight = (Cr,P,L,R)" by (cases ?tight, auto)
  from the_unique_root(5)[OF ur *(1)] have id2: "the_unique_root (p,l,r) = ?x" .
  have cr': "root_info_cond (?c ?p) ?p"
    by (rule count_roots_interval_sf_rat[OF p'])
  note ur = tighten_bound_root[OF n ur rc refl _ cr refl cr' refl tight p p' sgnl il(1), unfolded id2, OF refl]
  obtain ri p l r where norm: "?norm = (ri,p,l,r)" by (cases ?norm, auto)
  from the_unique_root(5)[OF ur(1-2)] 
  have id: "root n (rai_real x) = the_unique_root (P, L, R)"
    unfolding x tight rai_cond_def option.simps by (simp add: rai_real_def)
  note * = rai_normalize_poly_flat[OF norm[unfolded tight] ur(1,3,7)] 
  from * ur
  have "rai_cond y" unfolding y norm by (auto simp: rai_cond_def)
  thus ?thesis unfolding y norm unfolding id[symmetric] using *
    by (metis id norm rai_condD(8) the_equality unique_root_def unique_root_defs(2) y)
qed (simp add: y root_rai_fun_pos_def)

end

lemma root_rai_main: assumes x: "rai_cond x"
  defines y: "y \<equiv> root_rai_fun x"
  shows "rai_cond y \<and> (rai_real y = root n (rai_real x))"
proof -
  note y = y[unfolded root_rai_fun_def]
  show ?thesis
  proof (cases "n = 0")
    case True
    thus ?thesis unfolding y using of_rat_rai_main[of _ 0] by auto
  next
    case False note n = this
    note rt = root_rai_pos[OF n]
    show ?thesis
    proof (cases "sgn_rai_rat x \<ge> 0")
      case True
      from rt[OF x True] True n y show ?thesis by auto
    next
      case False
      let ?um = "uminus_rai_fun"
      let ?rt = "root_rai_fun_pos"
      note um = uminus_rai_main
      from n False y have y: "y = ?um (?rt (?um x))" by simp
      from um[OF x] have umx: "rai_cond (?um x)" and umx2: "rai_real (?um x) = - rai_real x" by auto
      have "sgn_rai_rat (?um x) = - sgn_rai_rat x" using x[unfolded rai_cond_def] 
        unfolding uminus_rai_fun_def sgn_rai_rat_def Let_def
        by (cases x, auto simp: sgn_minus_rat)
      with False have "0 \<le> sgn_rai_rat (?um x)" by simp
      from rt[OF umx this] umx2 have rumx: "rai_cond (?rt (?um x))" 
        and rumx2: "rai_real (?rt (?um x)) = root n (- rai_real x)"
        by auto
      from um[OF rumx] rumx2 y real_root_minus show ?thesis by auto
    qed
  qed
qed

lift_definition root_rai :: "real_alg_intern \<Rightarrow> real_alg_intern" is root_rai_fun
  by (insert root_rai_main, auto)
  
lemma root_rai: "real_of_rai (root_rai x) = root n (real_of_rai x)"
  by (transfer, insert root_rai_main, auto)
end

(* ********************* *)
subsubsection\<open>Addition\<close>

fun sub_interval :: "rat \<times> rat \<Rightarrow> rat \<times> rat \<Rightarrow> bool" where
  "sub_interval (l,r) (l',r') = (l' \<le> l \<and> r \<le> r')"

fun in_interval :: "rat \<times> rat \<Rightarrow> real \<Rightarrow> bool" where 
  "in_interval (l,r) x = (of_rat l \<le> x \<and> x \<le> of_rat r)" 

definition converges_to :: "(nat \<Rightarrow> rat \<times> rat) \<Rightarrow> real \<Rightarrow> bool" where
  "converges_to f x \<equiv> (\<forall> n. in_interval (f n) x \<and> sub_interval (f (Suc n)) (f n))
   \<and> (\<forall> (eps :: real) > 0. \<exists> n l r. f n = (l,r) \<and> of_rat r - of_rat l \<le> eps)"

context
  fixes bnd_update :: "'a \<Rightarrow> 'a" 
  and bnd_get :: "'a \<Rightarrow> rat \<times> rat"
begin

definition at_step :: "(nat \<Rightarrow> rat \<times> rat) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool" where
  "at_step f n a \<equiv> \<forall> i. bnd_get ((bnd_update ^^ i) a) = f (n + i)"

partial_function (tailrec) select_correct_factor_main
  :: "'a \<Rightarrow> (rat poly \<times> root_info)list \<Rightarrow> (rat poly \<times> root_info)list
    \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> (rat poly \<times> root_info) \<times> rat \<times> rat" where
  [code]: "select_correct_factor_main bnd todo old l r n = (case todo of Nil
    \<Rightarrow> if n = 1 then (hd old, l, r) else let bnd' = bnd_update bnd in (case bnd_get bnd' of (l,r) \<Rightarrow> 
      select_correct_factor_main bnd' old [] l r 0)
   | Cons (p,ri) todo \<Rightarrow> let m = root_info.l_r ri l r in 
      if m = 0 then select_correct_factor_main bnd todo old l r n
      else select_correct_factor_main bnd todo ((p,ri) # old) l r (n + m))"

definition select_correct_factor :: "'a \<Rightarrow> (rat poly \<times> root_info)list \<Rightarrow>
    (rat poly \<times> root_info) \<times> rat \<times> rat" where
  "select_correct_factor init polys = (case bnd_get init of (l,r) \<Rightarrow>
    select_correct_factor_main init polys [] l r 0)"

lemma select_correct_factor_main: assumes conv: "converges_to f x"
  and at: "at_step f i a"
  and res: "select_correct_factor_main a todo old l r n = ((q,ri_fin),(l_fin,r_fin))"
  and bnd: "bnd_get a = (l,r)"
  and ri: "\<And> q ri. (q,ri) \<in> set todo \<union> set old \<Longrightarrow> root_info_cond ri q"
  and q0: "\<And> q ri. (q,ri) \<in> set todo \<union> set old \<Longrightarrow> q \<noteq> 0"
  and ex: "\<exists>q. q \<in> fst ` set todo \<union> fst ` set old \<and> rpoly q x = 0"
  and dist: "distinct (map fst (todo @ old))"
  and old: "\<And> q ri. (q,ri) \<in> set old \<Longrightarrow> root_info.l_r ri l r \<noteq> 0"
  and un: "\<And> x :: real. (\<exists>q. q \<in> fst ` set todo \<union> fst ` set old \<and> rpoly q x = 0) \<Longrightarrow> 
    \<exists>!q. q \<in> fst ` set todo \<union> fst ` set old \<and> rpoly q x = 0"
  and n: "n = sum_list (map (\<lambda> (q,ri). root_info.l_r ri l r) old)"
  shows "unique_root (q,l_fin,r_fin) \<and> (q,ri_fin) \<in> set todo \<union> set old \<and> x = the_unique_root (q,l_fin,r_fin)"
proof -
  def orig \<equiv> "set todo \<union> set old"
  have orig: "set todo \<union> set old \<subseteq> orig" unfolding orig_def by auto
  let ?rts = "{x :: real. \<exists> q ri. (q,ri) \<in> orig \<and> rpoly q x = 0}"
  def rts \<equiv> ?rts
  let ?h = "\<lambda> (x,y). abs (x - y)" 
  let ?r = real_of_rat
  have rts: "?rts = (\<Union> ((\<lambda> (q,ri). {x. rpoly q x = 0}) ` set (todo @ old)))" unfolding orig_def by auto
  have "finite rts" unfolding rts rts_def
    using finite_rpoly_roots[OF q0] finite_set[of "todo @ old"] by auto  
  hence fin: "finite (rts \<times> rts - Id)" by auto   
  def diffs \<equiv> "insert 1 {abs (x - y) | x y. x \<in> rts \<and> y \<in> rts \<and> x \<noteq> y}"
  have "finite {abs (x - y) | x y. x \<in> rts \<and> y \<in> rts \<and> x \<noteq> y}"
    by (rule subst[of _ _ finite, OF _ finite_imageI[OF fin, of ?h]], auto)
  hence diffs: "finite diffs" "diffs \<noteq> {}" unfolding diffs_def by auto
  def eps \<equiv> "Min diffs / 2"
  have "\<And> x. x \<in> diffs \<Longrightarrow> x > 0" unfolding diffs_def by auto
  with Min_gr_iff[OF diffs] have eps: "eps > 0" unfolding eps_def by auto
  note conv = conv[unfolded converges_to_def] 
  from conv eps obtain N L R where 
    N: "f N = (L,R)" "?r R - ?r L \<le> eps" by auto
  obtain pair where pair: "pair = (todo,i)" by auto
  def rel \<equiv> "measures [ \<lambda> (t,i). N - i, \<lambda> (t :: (rat poly \<times> root_info) list,i). length t]"
  have wf: "wf rel" unfolding rel_def by simp
  show ?thesis
    using at res bnd ri q0 ex dist old un n pair orig
  proof (induct pair arbitrary: todo i old a l r n rule: wf_induct[OF wf])
    case (1 pair todo i old a l r n)
    note IH = 1(1)[rule_format]
    note at = 1(2)
    note res = 1(3)[unfolded select_correct_factor_main.simps[of _ todo]]
    note bnd = 1(4)
    note ri = 1(5)
    note q0 = 1(6)
    note ex = 1(7)
    note dist = 1(8)
    note old = 1(9)
    note un = 1(10)
    note n = 1(11)
    note pair = 1(12)
    note orig = 1(13)
    from at[unfolded at_step_def, rule_format, of 0] bnd have fi: "f i = (l,r)" by auto
    with conv have inx: "in_interval (f i) x" by blast
    hence lxr: "?r l \<le> x" "x \<le> ?r r" unfolding fi by auto
    from order.trans[OF this] have lr: "l \<le> r" unfolding of_rat_less_eq .
    show ?case 
    proof (cases todo)
      case (Cons rri tod)
      obtain s ri where rri: "rri = (s,ri)" by force
      with Cons have todo: "todo = (s,ri) # tod" by simp
      note res = res[unfolded todo list.simps split Let_def]
      from root_info_condD(1)[OF ri[of s ri, unfolded todo] lr]
      have ri': "root_info.l_r ri l r = card {x. root_cond (s, l, r) x}" by auto
      from q0 have s0: "s \<noteq> 0" unfolding todo by auto
      from finite_rpoly_roots[OF s0] have fins: "finite {x. root_cond (s, l, r) x}" 
        unfolding root_cond_def by auto
      have rel: "((tod,i), pair) \<in> rel" unfolding rel_def pair todo by simp
      show ?thesis
      proof (cases "root_info.l_r ri l r = 0")
        case True
        with res have res: "select_correct_factor_main a tod old l r n = ((q, ri_fin), l_fin, r_fin)" by auto
        from ri'[symmetric, unfolded True] fins have empty: "{x. root_cond (s, l, r) x} = {}" by simp
        from ex lxr empty have ex': "(\<exists>q. q \<in> fst ` set tod \<union> fst ` set old \<and> rpoly q x = 0)"
          unfolding todo root_cond_def split by auto
        have "unique_root (q, l_fin, r_fin) \<and> (q, ri_fin) \<in> set tod \<union> set old \<and> 
          x = the_unique_root (q, l_fin, r_fin)"
        proof (rule IH[OF rel at res bnd ri _ ex' _ _ _ n refl], goal_cases)
          case (5 y) thus ?case using un[of y] unfolding todo by auto
        next
          case 2 thus ?case using q0 unfolding todo by auto
        qed (insert dist old orig, auto simp: todo)
        thus ?thesis unfolding todo by auto
      next
        case False
        with res have res: "select_correct_factor_main a tod ((s, ri) # old) l r 
          (n + root_info.l_r ri l r) = ((q, ri_fin), l_fin, r_fin)" by auto
        from ex have ex': "\<exists>q. q \<in> fst ` set tod \<union> fst ` set ((s, ri) # old) \<and> rpoly q x = 0"
          unfolding todo by auto
        from dist have dist: "distinct (map fst (tod @ (s, ri) # old))" unfolding todo by auto
        have id: "set todo \<union> set old = set tod \<union> set ((s, ri) # old)" unfolding todo by simp
        show ?thesis unfolding id
        proof (rule IH[OF rel at res bnd ri _ ex' dist], goal_cases)
          case 4 thus ?case using un unfolding todo by auto
        qed (insert old False orig, auto simp: q0 todo n)
      qed
    next
      case Nil
      note res = res[unfolded Nil list.simps Let_def]
      from ex[unfolded Nil] lxr obtain s where "s \<in> fst ` set old \<and> root_cond (s,l,r) x"
        unfolding root_cond_def by auto
      then obtain q1 ri1 old' where old': "old = (q1,ri1) # old'" using id by (cases old, auto)
      let ?ri = "root_info.l_r ri1 l r"
      from old[unfolded old'] have 0: "?ri \<noteq> 0" by auto
      from n[unfolded old'] 0 have n0: "n \<noteq> 0" by auto
      from ri[unfolded old'] have ri': "root_info_cond ri1 q1" by auto
      show ?thesis
      proof (cases "n = 1")
        case False
        with n0 have n1: "n > 1" by auto
        obtain l' r' where bnd': "bnd_get (bnd_update a) = (l',r')" by force        
        with res False have res: "select_correct_factor_main (bnd_update a) old [] l' r' 0 =
          ((q, ri_fin), l_fin, r_fin)" by auto
        have at': "at_step f (Suc i) (bnd_update a)" unfolding at_step_def
        proof (intro allI, goal_cases)
          case (1 n)
          have id: "(bnd_update ^^ Suc n) a = (bnd_update ^^ n) (bnd_update a)"
            by (induct n, auto)
          from at[unfolded at_step_def, rule_format, of "Suc n"]
          show ?case unfolding id by simp
        qed
        from 0[unfolded root_info_condD(1)[OF ri' lr]] obtain y1 where y1: "root_cond (q1,l,r) y1" 
          by (cases "Collect (root_cond (q1, l, r)) = {}", auto)
        from n1[unfolded n old'] 
        have "?ri > 1 \<or> sum_list (map (\<lambda> (q,ri). root_info.l_r ri l r) old') \<noteq> 0"
          by (cases "sum_list (map (\<lambda> (q,ri). root_info.l_r ri l r) old')", auto)
        hence "\<exists> q2 ri2 y2. (q2,ri2) \<in> set old \<and> root_cond (q2,l,r) y2 \<and> y1 \<noteq> y2"
        proof
          assume "?ri > 1"
          with root_info_condD(1)[OF ri' lr] have "card {x. root_cond (q1, l, r) x} > 1" by simp
          from card_gt_1D[OF this] y1 obtain y2 where "root_cond (q1,l,r) y2" and "y1 \<noteq> y2" by auto
          thus ?thesis unfolding old' by auto
        next
          assume "sum_list (map (\<lambda> (q,ri). root_info.l_r ri l r) old') \<noteq> 0"
          then obtain q2 ri2 where mem: "(q2,ri2) \<in> set old'" and ri2: "root_info.l_r ri2 l r \<noteq> 0" by auto
          with q0 ri have "root_info_cond ri2 q2" unfolding old' by auto
          from ri2[unfolded root_info_condD(1)[OF this lr]] obtain y2 where y2: "root_cond (q2,l,r) y2"
            by (cases "Collect (root_cond (q2, l, r)) = {}", auto)
          from dist[unfolded old'] split_list[OF mem] have diff: "q1 \<noteq> q2" by auto
          from y1 have q1: "q1 \<in> fst ` set todo \<union> fst ` set old \<and> rpoly q1 y1 = 0"
            unfolding old' root_cond_def by auto
          from y2 have q2: "q2 \<in> fst ` set todo \<union> fst ` set old \<and> rpoly q2 y2 = 0"
            unfolding old' root_cond_def using mem by force
          have "y1 \<noteq> y2"
          proof
            assume id: "y1 = y2"
            from q1 have "\<exists> q1. q1 \<in> fst ` set todo \<union> fst ` set old \<and> rpoly q1 y1 = 0" by blast
            from un[OF this] q1 q2[folded id] have "q1 = q2" by auto
            with diff show False by simp
          qed
          with mem y2 show ?thesis unfolding old' by auto
        qed
        then obtain q2 ri2 y2 where 
          mem2: "(q2,ri2) \<in> set old" and y2: "root_cond (q2,l,r) y2" and diff: "y1 \<noteq> y2" by auto
        from mem2 orig have "(q1,ri1) \<in> orig" "(q2,ri2) \<in> orig"  unfolding old' by auto
        with y1 y2 diff have "abs (y1 - y2) \<in> diffs" unfolding diffs_def rts_def root_cond_def by auto
        from Min_le[OF diffs(1) this] have "abs (y1 - y2) \<ge> 2 * eps" unfolding eps_def by auto
        with eps have eps: "abs (y1 - y2) > eps" by auto
        from y1 y2 have l: "of_rat l \<le> min y1 y2" unfolding root_cond_def by auto
        from y1 y2 have r: "of_rat r \<ge> max y1 y2" unfolding root_cond_def by auto
        from l r eps have eps: "of_rat r - of_rat l > eps" by auto
        have "i < N" 
        proof (rule ccontr)
          assume "\<not> i < N"
          hence "\<exists> k. i = N + k" by presburger
          then obtain k where i: "i = N + k" by auto
          {
            fix k l r
            assume "f (N + k) = (l,r)"
            hence "of_rat r - of_rat l \<le> eps"
            proof (induct k arbitrary: l r)
              case 0
              with N show ?case by auto
            next
              case (Suc k l r)
              obtain l' r' where f: "f (N + k) = (l',r')" by force
              from Suc(1)[OF this] have IH: "?r r' - ?r l' \<le> eps" by auto
              from f Suc(2) conv[THEN conjunct1, rule_format, of "N + k"] 
              have "?r l \<ge> ?r l'" "?r r \<le> ?r r'"
                by (auto simp: of_rat_less_eq)
              thus ?case using IH by auto
            qed
          } note * = this
          from at[unfolded at_step_def i, rule_format, of 0] bnd  have "f (N + k) = (l,r)" by auto
          from *[OF this] eps
          show False by auto
        qed
        hence rel: "((old, Suc i), pair) \<in> rel" unfolding pair rel_def by auto
        from dist have dist: "distinct (map fst (old @ []))" unfolding Nil by auto
        have id: "set todo \<union> set old = set old \<union> set []" unfolding Nil by auto
        show ?thesis unfolding id
        proof (rule IH[OF rel at' res bnd' ri _ _ dist _ _ _ refl], goal_cases)
          case 2 thus ?case using q0 by auto
        qed (insert ex un orig Nil, auto)
      next
        case True
        with res old' have id: "q = q1" "ri_fin = ri1" "l_fin = l" "r_fin = r" by auto
        from n[unfolded True old'] 0 have 1: "?ri = 1" 
          by (cases ?ri; cases "?ri - 1", auto)
        from root_info_condD(1)[OF ri' lr] 1 have "card {x. root_cond (q1,l,r) x} = 1" by auto
        from card_1_Collect_ex1[OF this]
        have unique: "unique_root (q1,l,r)" unfolding unique_root_def .
        from ex[unfolded Nil old'] consider (A) "rpoly q1 x = 0" 
          | (B) q where "q \<in> fst ` set old'" "rpoly q x = 0" by auto
        hence "x = the_unique_root (q1,l,r)"
        proof (cases)
          case A
          with lxr have "root_cond (q1,l,r) x" unfolding root_cond_def by auto
          from the_unique_root(5)[OF unique this] show ?thesis by simp
        next
          case (B q)
          with lxr have "root_cond (q,l,r) x" unfolding root_cond_def by auto
          hence empty: "{x. root_cond (q,l,r) x} \<noteq> {}" by auto
          from B(1) obtain ri' where mem: "(q,ri') \<in> set old'" by force
          from q0[unfolded old'] mem have q0: "q \<noteq> 0" by auto
          from finite_rpoly_roots[OF this] have "finite {x. root_cond (q,l,r) x}" 
            unfolding root_cond_def by auto
          with empty have card: "card {x. root_cond (q,l,r) x} \<noteq> 0" by simp
          from ri[unfolded old'] mem have "root_info_cond ri' q" by auto
          from root_info_condD(1)[OF this lr] card have "root_info.l_r ri' l r \<noteq> 0" by auto
          with n[unfolded True old'] 1 split_list[OF mem] have False by auto
          thus ?thesis by simp
        qed
        thus ?thesis unfolding id using unique ri' unfolding old' by auto
      qed
    qed
  qed
qed

lemma select_correct_factor: assumes 
      conv: "converges_to (\<lambda> i. bnd_get ((bnd_update ^^ i) init)) x"
  and res: "select_correct_factor init polys = ((q,ri),(l,r))"
  and ri: "\<And> q ri. (q,ri) \<in> set polys \<Longrightarrow> root_info_cond ri q"
  and q0: "\<And> q ri. (q,ri) \<in> set polys \<Longrightarrow> q \<noteq> 0"
  and ex: "\<exists>q. q \<in> fst ` set polys \<and> rpoly q x = 0"
  and dist: "distinct (map fst polys)"
  and un: "\<And> x :: real. (\<exists>q. q \<in> fst ` set polys \<and> rpoly q x = 0) \<Longrightarrow> 
    \<exists>!q. q \<in> fst ` set polys \<and> rpoly q x = 0"
  shows "unique_root (q,l,r) \<and> (q,ri) \<in> set polys \<and> x = the_unique_root (q,l,r)"
proof -
  obtain l' r' where init: "bnd_get init = (l',r')" by force
  from res[unfolded select_correct_factor_def init split]
  have res: "select_correct_factor_main init polys [] l' r' 0 = ((q, ri), l, r)" by auto
  have at: "at_step (\<lambda> i. bnd_get ((bnd_update ^^ i) init)) 0 init" unfolding at_step_def by auto
  have "unique_root (q,l,r) \<and> (q,ri) \<in> set polys \<union> set [] \<and> x = the_unique_root (q,l,r)"
    by (rule select_correct_factor_main[OF conv at res init ri], insert dist un ex q0, auto)
  thus ?thesis by auto
qed

definition mk_rai_intern :: "root_info \<Rightarrow> rat poly \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rai_intern" where
  "mk_rai_intern ri p l r = (if l \<le> 0 \<and> 0 \<le> r \<and> coeff p 0 = 0 then None 
     else case tighten_poly_bounds_for_x (root_info.l_r ri) 0 l r of
              (l',r') \<Rightarrow> Some (ri,p,l',r'))"

lemma mk_rai_intern: assumes ur: "unique_root (q,l,r)" and pt: "poly_cond q"
  and ri: "root_info_cond ri q"
  shows "rai_cond (mk_rai_intern ri q l r) \<and> 
    rai_real (mk_rai_intern ri q l r) = the_unique_root (q,l,r)"
proof -
  let ?rai = "mk_rai_intern ri q l r"
  let ?r = real_of_rat
  interpret inj_field_hom ?r .. 
  have "coeff q 0 = 0 \<longleftrightarrow> poly q 0 = 0" by (simp add: poly_0_coeff_0)
  also have "\<dots> \<longleftrightarrow> poly (map_poly ?r q) (?r 0) = (?r 0)" unfolding rpoly.poly_map_poly by auto
  also have "\<dots> \<longleftrightarrow> rpoly q 0 = (0 :: real)" by (auto simp: eval_poly_def)
  finally have id: "coeff q 0 = 0 \<longleftrightarrow> rpoly q 0 = (0 :: real)" .
  have id: "(l \<le> 0 \<and> 0 \<le> r \<and> coeff q 0 = 0) = root_cond (q,l,r) 0"
    unfolding id root_cond_def by auto
  show ?thesis
  proof (cases "root_cond (q,l,r) 0")
    case True
    hence rai: "?rai = None" unfolding mk_rai_intern_def id by auto
    from the_unique_root(5)[OF ur True] rai show ?thesis by auto
  next
    case False
    obtain l' r' where tight: "tighten_poly_bounds_for_x (root_info.l_r ri) 0 l r = (l',r')" by force
    have rai': "?rai = Some (ri, q, l', r')"
      unfolding mk_rai_intern_def using False[folded id] tight by auto
    hence rai: "rai_real ?rai = the_unique_root (q,l',r')" unfolding rai_real_def by auto    
    have "l \<le> 0 \<Longrightarrow> 0 \<le> r \<Longrightarrow> poly q 0 \<noteq> 0" using False[folded id poly_0_coeff_0] by auto   
    note tight = tighten_poly_bounds_for_x[OF ur this refl ri refl tight]
    let ?x = "the_unique_root (q, l, r)"    
    from tight have tight: "root_cond (q,l',r') ?x" "l \<le> l'" "l' \<le> r'" "r' \<le> r" "l' > 0 \<or> r' < 0" by auto
    from unique_root_sub_interval[OF ur tight(1) tight(2,4)] 
    have ur': "unique_root (q, l', r')" and x: "?x = the_unique_root (q,l',r')" by auto
    from tight(2-) have sgn: "sgn l' = sgn r'" "sgn r' \<noteq> 0" by auto
    have q0: "q \<noteq> 0" using poly_cond_D pt by force
    show "rai_cond ?rai \<and> rai_real ?rai = ?x" unfolding rai'
    proof (rule rai_cond_realI[OF tight(1) q0 sgn _ ri pt])
      fix y
      assume "root_cond (q,l',r') y"
      from the_unique_root(5)[OF ur' this] x show "?x = y" by auto
    qed
  qed
qed

definition select_correct_factor_rat_poly :: "'a \<Rightarrow> rat poly \<Rightarrow> rai_intern" where
  "select_correct_factor_rat_poly init p \<equiv> 
     let qs = factors_of_rat_poly p;
         polys = map (\<lambda> q. (q, count_roots_interval_rat q)) qs;
         (* TODO: make choice on generic count_roots_interval_rat q or special case for linear q *)
         ((q,ri),(l,r)) = select_correct_factor init polys
      in mk_rai_intern ri q l r"

lemma select_correct_factor_rat_poly: assumes 
      conv: "converges_to (\<lambda> i. bnd_get ((bnd_update ^^ i) init)) x"
  and rai: "select_correct_factor_rat_poly init p = rai"
  and x: "rpoly p x = 0"
  and p: "p \<noteq> 0"
  shows "rai_cond rai \<and> rai_real rai = x"
proof -
  obtain qs where fact: "factors_of_rat_poly p = qs" by auto
  def polys \<equiv> "map (\<lambda> q. (q, count_roots_interval_rat q)) qs"
  obtain q ri l r where res: "select_correct_factor init polys = ((q,ri),(l,r))"
    by (cases "select_correct_factor init polys", auto)
  have fst: "map fst polys = qs" "fst ` set polys = set qs" unfolding polys_def map_map o_def 
    by force+
  note fact' = factors_of_rat_poly[OF fact]
  note rai = rai[unfolded select_correct_factor_rat_poly_def Let_def fact, 
    folded polys_def, unfolded res split]
  from fact' fst have dist: "distinct (map fst polys)" by auto
  from fact'(2)[OF p, of x] x fst 
  have ex: "\<exists>q. q \<in> fst ` set polys \<and> rpoly q x = 0" by auto
  {
    fix q ri
    assume "(q,ri) \<in> set polys"
    hence ri: "ri = count_roots_interval_rat q" and q: "q \<in> set qs" unfolding polys_def by auto
    from fact'(1)[OF q] have *: "monic q" "irreducible q" by auto
    from irreducible_square_free[OF *(2)] have sf: "square_free q" .
    from * have q0: "q \<noteq> 0" by auto
    from count_roots_interval_rat[OF sf] ri have ri: "root_info_cond ri q" by simp
    note ri q0 *
  } note polys = this
  have "unique_root (q, l, r) \<and> (q, ri) \<in> set polys \<and> x = the_unique_root (q, l, r)"
    by (rule select_correct_factor[OF conv res polys(1) _ ex dist, unfolded fst, OF _ _ fact'(3)[OF p]],
    insert fact'(2)[OF p] polys(2), auto)
  hence ur: "unique_root (q,l,r)" and mem: "(q,ri) \<in> set polys" and x: "x = the_unique_root (q,l,r)" by auto   
  note polys = polys[OF mem]
  from polys(3-4) have ty: "poly_cond q" by (simp add: poly_cond_def)
  show ?thesis unfolding x rai[symmetric]
    by (rule mk_rai_intern[OF ur ty polys(1)])
qed
end


(* addition *)
context
begin
private fun add_rat_rai_fun :: "rat \<Rightarrow> rai_intern \<Rightarrow> rai_intern" where
  "add_rat_rai_fun r1 (Some (ri2,p2,l2,r2)) = (
    let p = monic_poly (poly_add_rat r1 p2);
      ri = count_roots_interval_rat p;
      cr = root_info.l_r ri;
      (l,r) = (l2+r1,r2+r1)
    in if l \<le> 0 \<and> 0 \<le> r \<and> poly p 0 = 0 then None else 
      let (l,r) = tighten_poly_bounds_for_x cr 0 l r
      in Some (ri,p,l,r))"
| "add_rat_rai_fun r1 None = of_rat_rai_fun r1"

definition normalize_rat_poly :: "rat poly \<Rightarrow> rat poly" where
  "normalize_rat_poly p = map_poly of_int (snd (rat_to_int_poly p))"

lemma normalize_rat_poly[simp]: "alg_poly x (normalize_rat_poly p) = alg_poly x p" 
  "rpoly (normalize_rat_poly p) y = 0 \<longleftrightarrow> rpoly p y = 0" "normalize_rat_poly p = 0 \<longleftrightarrow> p = 0"
proof -
  obtain d q where ri: "rat_to_int_poly p = (d,q)" by force
  from rat_to_int_poly[OF this] obtain d where p: "p = smult (inverse d) (map_poly of_int q)" and d: "d \<noteq> 0" by auto
  from arg_cong[OF p, of "smult d"] d have q: "map_poly of_int q = smult d p" by simp
  hence id: "normalize_rat_poly p = smult d p" using ri unfolding normalize_rat_poly_def by auto
  show rp: "\<And> y. rpoly (normalize_rat_poly p) y = 0 \<longleftrightarrow> rpoly p y = 0" unfolding id
    by (metis (no_types, lifting) inverse_zero of_rat_inverse p poly_smult_zero_iff rpoly.map_poly_smult rpoly.poly_map_poly_eval_poly)
  show norm: "normalize_rat_poly p = 0 \<longleftrightarrow> p = 0" unfolding id using d by auto
  show "alg_poly x (normalize_rat_poly p) = alg_poly x p" unfolding alg_poly_def norm rp by auto
qed

lemma normalize_rat_poly2[simp]: "root_info_cond r (normalize_rat_poly p) = root_info_cond r p"
  "unique_root (normalize_rat_poly p, x, y) = unique_root (p, x, y)"
  "the_unique_root (normalize_rat_poly p,x,y) = the_unique_root (p,x,y)"
  unfolding root_info_cond_def root_cond_def unique_root_def the_unique_root_def by auto

fun tighten_poly_bounds_binary :: "(rat \<Rightarrow> rat \<Rightarrow> nat) \<Rightarrow> (rat \<Rightarrow> rat \<Rightarrow> nat) \<Rightarrow> 
  (rat \<times> rat) \<times> (rat \<times> rat) \<Rightarrow> (rat \<times> rat) \<times> (rat \<times> rat)" where
  "tighten_poly_bounds_binary cr1 cr2 ((l1,r1),(l2,r2)) = 
     (tighten_poly_bounds cr1 l1 r1, tighten_poly_bounds cr2 l2 r2)"

lemma tighten_poly_bounds_binary: assumes cr1: "root_info_cond ri1 p1" "cr1 = root_info.l_r ri1"
  and cr2: "root_info_cond ri2 p2" "cr2 = root_info.l_r ri2" 
  and ur: "unique_root (p1,l1,r1)" "unique_root (p2,l2,r2)"
  and xy: "x = the_unique_root (p1,l1,r1)" "y = the_unique_root (p2,l2,r2)"
  and bnd: "\<And> l1 r1 l2 r2 l r. I l1 \<Longrightarrow> I l2 \<Longrightarrow> root_cond (p1,l1,r1) x \<Longrightarrow> root_cond (p2,l2,r2) y \<Longrightarrow>
      bnd ((l1,r1),(l2,r2)) = (l,r) \<Longrightarrow> of_rat l \<le> f x y \<and> f x y \<le> of_rat r"
  and approx: "\<And> l1 r1 l2 r2 l1' r1' l2' r2' l l' r r'. 
    I l1 \<Longrightarrow> I l2 \<Longrightarrow>
    l1 \<le> r1 \<Longrightarrow> l2 \<le> r2 \<Longrightarrow> 
    (l,r) = bnd ((l1,r1), (l2,r2)) \<Longrightarrow>
    (l',r') = bnd ((l1',r1'), (l2',r2')) \<Longrightarrow>
    (l1',r1') \<in> {(l1,(l1+r1)/2),((l1+r1)/2,r1)} \<Longrightarrow>
    (l2',r2') \<in> {(l2,(l2+r2)/2),((l2+r2)/2,r2)} \<Longrightarrow>
    (r' - l') \<le> 3/4 * (r - l) \<and> l \<le> l' \<and> r' \<le> r"
  and I_mono: "\<And> l l'. I l \<Longrightarrow> l \<le> l' \<Longrightarrow> I l'"
  and I: "I l1" "I l2" 
  shows "converges_to (\<lambda> i. bnd ((tighten_poly_bounds_binary cr1 cr2 ^^ i) ((l1,r1),(l2,r2))))
     (f x y)"
proof -
  let ?upd = "tighten_poly_bounds_binary cr1 cr2"
  def upd \<equiv> ?upd
  def init \<equiv> "((l1, r1), l2, r2)"
  let ?g = "(\<lambda>i. bnd ((upd ^^ i) init))"
  obtain l r where bnd_init: "bnd init = (l,r)" by force
  note ur1 = the_unique_root[OF ur(1)]
  note ur2 = the_unique_root[OF ur(2)]
  from ur1(4) ur2(4) xy 
  have rc1: "root_cond (p1,l1,r1) x" and rc2: "root_cond (p2,l2,r2) y" by auto
  def g \<equiv> ?g
  {
    fix i L1 R1 L2 R2 L R j
    assume "((upd ^^ i)) init = ((L1,R1),(L2,R2))" "g i = (L,R)"
    hence "I L1 \<and> I L2 \<and> root_cond (p1,L1,R1) x \<and> root_cond (p2,L2,R2) y \<and>
      unique_root (p1, L1, R1) \<and> unique_root (p2, L2, R2) \<and> in_interval (L,R) (f x y) \<and> 
      (i = Suc j \<longrightarrow> sub_interval (g i) (g j) \<and> (R - L \<le> 3/4 * (snd (g j) - fst (g j))))"
    proof (induct i arbitrary: L1 R1 L2 R2 L R j)
      case 0
      thus ?case using I rc1 rc2 ur bnd[of l1 l2 r1 r2 L R] g_def unfolding init_def by auto
    next
      case (Suc i)
      obtain l1 r1 l2 r2 where updi: "(upd ^^ i) init = ((l1, r1), l2, r2)" by (cases "(upd ^^ i) init", auto)
      obtain l r where bndi: "bnd ((l1, r1), l2, r2) = (l,r)" by force
      hence gi: "g i = (l,r)" using updi unfolding g_def by auto
      have "(upd ^^ Suc i) init = upd ((l1, r1), l2, r2)" using updi by simp
      from Suc(2)[unfolded this] have upd: "upd ((l1, r1), l2, r2) = ((L1, R1), L2, R2)" .
      from upd updi Suc(3) have bndsi: "bnd ((L1, R1), L2, R2) = (L,R)" by (auto simp: g_def)
      from Suc(1)[OF updi gi] have I: "I l1" "I l2" 
        and rc: "root_cond (p1,l1,r1) x" "root_cond (p2,l2,r2) y"
        and ur: "unique_root (p1, l1, r1)" "unique_root (p2, l2, r2)"
        by auto
      from upd[unfolded upd_def] 
      have tight: "tighten_poly_bounds cr1 l1 r1 = (L1, R1)" "tighten_poly_bounds cr2 l2 r2 = (L2, R2)"
        by auto
      note tight1 = tighten_poly_bounds[OF tight(1) ur(1) cr1]
      note tight2 = tighten_poly_bounds[OF tight(2) ur(2) cr2]
      from tight1 have lr1: "l1 \<le> r1" by auto
      from tight2 have lr2: "l2 \<le> r2" by auto
      note ur1 = the_unique_root[OF ur(1)]
      note ur2 = the_unique_root[OF ur(2)]
      from tight1 I_mono[OF I(1)] have I1: "I L1" by auto
      from tight2 I_mono[OF I(2)] have I2: "I L2" by auto
      note ur1 = unique_root_sub_interval[OF ur(1) tight1(1,2,4)]
      note ur2 = unique_root_sub_interval[OF ur(2) tight2(1,2,4)]
      from the_unique_root(5)[OF ur(1) rc(1)] ur1 have x: "x = the_unique_root (p1,L1,R1)" by simp
      from the_unique_root(5)[OF ur(2) rc(2)] ur2 have y: "y = the_unique_root (p2,L2,R2)" by simp
      from the_unique_root(4)[OF ur1(1)] x have x: "root_cond (p1,L1,R1) x" by auto
      from the_unique_root(4)[OF ur2(1)] y have y: "root_cond (p2,L2,R2) y" by auto
      from tight(1) have half1: "(L1, R1) \<in> {(l1, (l1 + r1) / 2), ((l1 + r1) / 2, r1)}"
        unfolding tighten_poly_bounds_def Let_def by (auto split: if_splits)
      from tight(2) have half2: "(L2, R2) \<in> {(l2, (l2 + r2) / 2), ((l2 + r2) / 2, r2)}"
        unfolding tighten_poly_bounds_def Let_def by (auto split: if_splits)
      from approx[OF I lr1 lr2 bndi[symmetric] bndsi[symmetric] half1 half2]
      have "R - L \<le> 3 / 4 * (r - l) \<and> l \<le> L \<and> R \<le> r" .
      hence "sub_interval (g (Suc i)) (g i)" "R - L \<le> 3/4 * (snd (g i) - fst (g i))" 
        unfolding gi Suc(3) by auto
      with bnd[OF I1 I2 x y bndsi]
      show ?case using I1 I2 x y ur1 ur2 by auto
    qed
  } note invariants = this
  def L \<equiv> "\<lambda> i. fst (g i)"
  def R \<equiv> "\<lambda> i. snd (g i)" 
  {
    fix i
    obtain l1 r1 l2 r2 where updi: "(upd ^^ i) init = ((l1, r1), l2, r2)" by (cases "(upd ^^ i) init", auto)
    obtain l r where bnd': "bnd ((l1, r1), l2, r2) = (l,r)" by force
    have gi: "g i = (l,r)" unfolding g_def updi bnd' by auto
    hence id: "l = L i" "r = R i" unfolding L_def R_def by auto
    from invariants[OF updi gi[unfolded id]] 
    have "in_interval (L i, R i) (f x y)" 
      "\<And> j. i = Suc j \<Longrightarrow> sub_interval (g i) (g j) \<and> R i - L i \<le> 3 / 4 * (R j - L j)"
      unfolding L_def R_def by auto
  } note * = this
  {
    fix i
    from *(1)[of i] *(2)[of "Suc i", OF refl]
    have "in_interval (g i) (f x y)" "sub_interval (g (Suc i)) (g i)" 
      "R (Suc i) - L (Suc i) \<le> 3 / 4 * (R i - L i)" unfolding L_def R_def by auto
  } note * = this
  show ?thesis unfolding upd_def[symmetric] init_def[symmetric] g_def[symmetric]
    unfolding converges_to_def 
  proof (intro conjI allI impI, rule *(1), rule *(2))
    fix eps :: real
    assume eps: "0 < eps"
    let ?r = real_of_rat 
    def r \<equiv> "\<lambda> n. ?r (R n)" 
    def l \<equiv> "\<lambda> n. ?r (L n)"
    def diff \<equiv> "\<lambda> n. r n - l n" 
    {
      fix n
      from *(3)[of n] have "?r (R (Suc n) - L (Suc n)) \<le> ?r (3 / 4 * (R n - L n))"
        unfolding of_rat_less_eq by simp
      also have "?r (R (Suc n) - L (Suc n)) = (r (Suc n) - l (Suc n))"
        unfolding of_rat_diff r_def l_def by simp
      also have "?r (3 / 4 * (R n - L n)) = 3 / 4 * (r n - l n)" 
        unfolding r_def l_def of_rat_diff[symmetric] by simp
      finally have "diff (Suc n) \<le> 3 / 4 * diff n" unfolding diff_def .
    } note * = this
    {
      fix i
      have "diff i \<le> (3/4)^i * diff 0" 
      proof (induct i)
        case (Suc i)
        from Suc *[of i] show ?case by auto
      qed auto
    }
    then obtain c where *: "\<And> i. diff i \<le> (3/4)^i * c" by auto
    have "\<exists> n. diff n \<le> eps"
    proof (cases "c \<le> 0")
      case True
      with *[of 0] eps show ?thesis by (intro exI[of _ 0], auto)
    next
      case False  
      hence c: "c > 0" by auto
      with eps have "inverse c * eps > 0" by auto
      from exp_tends_to_zero[of "3/4 :: real", OF _ _ this] obtain n where 
        "(3/4) ^ n \<le> inverse c * eps" by auto
      from mult_right_mono[OF this, of c] c
      have "(3/4) ^ n * c \<le> eps" by (auto simp: field_simps)
      with *[of n] show ?thesis by (intro exI[of _ n], auto)
    qed
    then obtain n where "?r (R n) - ?r (L n) \<le> eps" unfolding l_def r_def diff_def by blast
    thus "\<exists>n l r. g n = (l, r) \<and> ?r r - ?r l \<le> eps" unfolding L_def R_def by (intro exI[of _ n], force)
  qed
qed

private fun add_rai_fun :: "rai_intern \<Rightarrow> rai_intern \<Rightarrow> rai_intern" where
  "add_rai_fun (Some (ri1,p1,l1,r1)) (Some (ri2,p2,l2,r2)) = (
     select_correct_factor_rat_poly
       (tighten_poly_bounds_binary (root_info.l_r ri1) (root_info.l_r ri2))
       (\<lambda> ((l1,r1),(l2,r2)). (l1 + l2, r1 + r2))
       ((l1,r1),(l2,r2)) 
       (poly_add (normalize_rat_poly p1) (normalize_rat_poly p2)))"
| "add_rai_fun None y = y"
| "add_rai_fun x None = x"

lemma add_rai_main: assumes x: "rai_cond x" and y: "rai_cond y"
  defines z: "z \<equiv> add_rai_fun x y"
  shows "rai_cond z \<and> (rai_real z = rai_real x + rai_real y)"
proof (cases x)
  case None
  with y show ?thesis unfolding z by simp
next
  case (Some xt) note xt = this
  show ?thesis
  proof (cases y)
    case None
    with x y show ?thesis unfolding z xt by simp
  next
    case (Some yt) note yt = this
    obtain ri1 p1 l1 r1 where xt: "x = Some (ri1,p1,l1,r1)" unfolding xt by (cases xt, auto)
    obtain ri2 p2 l2 r2 where yt: "y = Some (ri2,p2,l2,r2)" unfolding yt by (cases yt, auto)
    let ?x = "rai_real (Some ( ri1, p1, l1, r1))"
    let ?y = "rai_real (Some ( ri2, p2, l2, r2))"
    let ?p1 = "normalize_rat_poly p1"
    let ?p2 = "normalize_rat_poly p2"
    let ?p = "poly_add ?p1 ?p2"    
    let ?lr = "root_info.l_r"
    note x = rai_condD[OF x[unfolded xt]]
    note y = rai_condD[OF y[unfolded yt]]
    from x(1,5) have ax: "alg_poly ?x ?p1" unfolding root_cond_def alg_poly_def by simp
    from y(1,5) have ay: "alg_poly ?y ?p2" unfolding root_cond_def alg_poly_def by simp
    from alg_poly_add_real[OF ax ay] have axy: "alg_poly (?x + ?y) ?p" .
    from alg_polyD[OF this] have p: "?p \<noteq> 0" and rt: "rpoly ?p (?x + ?y) = 0" .
    let ?bnd = "(\<lambda>((l1, r1), l2 :: rat, r2 :: rat). (l1 + l2, r1 + r2))"
    def bnd \<equiv> ?bnd
    from z[unfolded xt yt, simplified] have sel: "select_correct_factor_rat_poly
        (tighten_poly_bounds_binary (?lr ri1) (?lr ri2))
        bnd 
        ((l1, r1), l2, r2)
        (poly_add (normalize_rat_poly p1) (normalize_rat_poly p2)) = z" by (auto simp: bnd_def)
    have "rai_cond z \<and> rai_real z = ?x + ?y"
    proof (rule select_correct_factor_rat_poly[OF _ sel rt p])
      have tur: "?x = the_unique_root (p1,l1,r1)" "?y = the_unique_root (p2,l2,r2)"
        unfolding rai_real_def by auto
      show "converges_to
        (\<lambda>i. bnd ((tighten_poly_bounds_binary (root_info.l_r ri1) (root_info.l_r ri2) ^^ i)
        ((l1, r1), l2, r2))) (?x + ?y)"
        by (rule tighten_poly_bounds_binary[OF x(9) _ y(9) _ x(7) y(7) tur, 
          where f = "op +" and I = "\<lambda> _. True"], auto simp: bnd_def root_cond_def)
    qed
    thus ?thesis unfolding xt yt .
  qed
qed

lemma add_rat_rai_main: fixes r1 :: rat assumes y: "rai_cond y"
  defines z: "z \<equiv> add_rat_rai_fun r1 y"
  shows "rai_cond z \<and> (rai_real z = of_rat r1 + rai_real y)" 
proof (cases y)
  case None
  with y show ?thesis unfolding z using of_rat_rai_main[OF refl, of r1] by simp
next
  case (Some yt) note yt = this
  obtain ri2 p2 l2 r2 where yt: "y = Some (ri2,p2,l2,r2)" unfolding yt by (cases yt, auto)
  let ?x = "real_of_rat r1"
  let ?y = "rai_real (Some ( ri2, p2, l2, r2))"
  let ?p = "poly_add_rat r1 p2"    
  let ?mp = "monic_poly ?p"
  let ?ri = "count_roots_interval_rat ?mp"
  let ?lr = "root_info.l_r"
  note y = rai_condD[OF y[unfolded yt]]
  from y(5) have p: "?p \<noteq> 0" by simp
  hence mp: "?mp \<noteq> 0" by (simp add: monic_poly)
  from y(1)[unfolded root_cond_def split] 
  have rt: "rpoly p2 ?y = 0" and bnd: "of_rat l2 \<le> ?y" "?y \<le> of_rat r2" by auto
  from rt have rt: "rpoly ?p (?x + ?y) = 0" unfolding rpoly_add_rat by simp
  from poly_cond_D[OF y(10)] have "square_free p2" by simp
  hence sf: "square_free ?mp" unfolding monic_poly by (rule poly_add_rat_square_free)
  have mon: "monic ?mp" by (rule monic_poly(2)[OF p])
  note ri = count_roots_interval_rat[OF sf]
  obtain l r where lr: "l = l2 + r1" "r = r2 + r1" by force
  from bnd have bnd: "of_rat l \<le> ?x + ?y" "?x + ?y \<le> of_rat r" unfolding lr of_rat_add by auto
  with rt have rc: "root_cond (?mp,l,r) (?x + ?y)" unfolding root_cond_def by (auto simp: monic_poly)
  have ur: "unique_root (?mp,l,r)" unfolding unique_root_def
  proof (rule ex1I, rule rc)
    fix z
    assume "root_cond (?mp,l,r) z"
    from this[unfolded root_cond_def split] have bndz: "of_rat l \<le> z" "z \<le> of_rat r" 
      and rt: "rpoly ?mp z = 0" by auto
    from rt have rt: "rpoly p2 (z - ?x) = 0" unfolding monic_poly rpoly_add_rat .
    from bndz have "of_rat l2 \<le> z - ?x" "z - ?x \<le> of_rat r2" unfolding lr of_rat_add by auto
    with rt have "root_cond (p2,l2,r2) (z - ?x)" unfolding root_cond_def by auto
    from y(8)[OF this] have "?y = z - ?x" by auto
    thus "z = ?x + ?y" by auto
  qed
  from the_unique_root(5)[OF ur rc] have xy: "?x + ?y = the_unique_root (?mp,l,r)" by auto
  note z = z[unfolded yt, simplified, unfolded Let_def lr[symmetric] split]
  show ?thesis
  proof (cases "l \<le> 0 \<and> 0 \<le> r \<and> poly ?mp 0 = 0")
    case True
    hence "root_cond (?mp,l,r) 0" unfolding root_cond_def by simp
      (metis rpoly.eval_poly_poly rpoly.hom_zero)
    from the_unique_root(5)[OF ur this] xy have xy: "?x + ?y = 0" by simp
    with True z show ?thesis unfolding yt by simp
  next
    case False
    hence 0: "l \<le> 0 \<Longrightarrow> 0 \<le> r \<Longrightarrow> poly ?mp 0 \<noteq> 0" by auto
    let ?ri = "count_roots_interval_rat ?mp"
    obtain l' r' where tx: "tighten_poly_bounds_for_x (?lr ?ri) 0 l r = (l',r')" by force
    with z False have z: "z = Some (?ri, ?mp, l', r')" by auto
    from tighten_poly_bounds_for_x[OF ur 0 xy ri refl tx] 
    have lr'': "l \<le> l'" "r' \<le> r" and lr': "l' \<le> r'" and 
      rc: "root_cond (?mp, l', r') (?x + ?y)" and zero: "\<not> (l' \<le> 0 \<and> 0 \<le> r')" 
      by blast+
    from unique_root_sub_interval[OF ur rc[unfolded xy] lr''] have ur: "unique_root (?mp, l', r')"
      and tur: "the_unique_root (?mp,l',r') = ?x + ?y" unfolding xy by auto
    have yp2: "alg_poly ?y p2" using y(1,5) unfolding root_cond_def split alg_poly_def by auto
    from poly_add_rat_irreducible poly_cond_D[OF y(10)] y(5) 
    have "irreducible ?mp"  "monic ?mp" by (auto simp: monic_poly(1-3))
    with sf mon have un: "poly_cond ?mp" by (auto simp: poly_cond_def)
    have rc: "rai_cond (Some (?ri, ?mp, l', r'))"
      unfolding rai_cond_def using zero lr' un
      by (auto simp: ur mp ri)
    show ?thesis unfolding z using rc tur yt by (simp add: rai_real_def)
  qed
qed

lift_definition add_rai :: "real_alg_intern \<Rightarrow> real_alg_intern \<Rightarrow> real_alg_intern" is add_rai_fun
  by (insert add_rai_main, auto)
  
lemma add_rai: "real_of_rai (add_rai x y) = real_of_rai x + real_of_rai y"
  by (transfer, insert add_rai_main, auto)

lift_definition add_rat_rai :: "rat \<Rightarrow> real_alg_intern \<Rightarrow> real_alg_intern" is add_rat_rai_fun
  by (insert add_rat_rai_main, auto)
  
lemma add_rat_rai: "real_of_rai (add_rat_rai x y) = of_rat x + real_of_rai y"
  by (transfer, insert add_rat_rai_main, auto)
end

(* ********************* *)
subsubsection\<open>Multiplication\<close>

context
begin
private fun mult_rat_rai_fun_pos :: "rat \<Rightarrow> rai_intern_flat \<Rightarrow> rai_intern_flat" where
  "mult_rat_rai_fun_pos r1 (ri2,p2,l2,r2) = (
    let p = monic_poly (poly_mult_rat r1 p2);
      ri = count_roots_interval_rat p;
      cr = root_info.l_r ri;
      (l,r) = (l2*r1,r2*r1)
    in (ri,p,l,r))"

private fun mult_rai_fun_pos :: "rai_intern_flat \<Rightarrow> rai_intern_flat \<Rightarrow> rai_intern_flat" where
  "mult_rai_fun_pos (ri1,p1,l1,r1) (ri2,p2,l2,r2) = (
      the (select_correct_factor_rat_poly 
        (tighten_poly_bounds_binary (root_info.l_r ri1) (root_info.l_r ri2))
        (\<lambda> ((l1,r1),(l2,r2)). (l1 * l2, r1 * r2))
        ((l1,r1),(l2,r2))
        (poly_mult (normalize_rat_poly p1) (normalize_rat_poly p2))))"

private fun mult_rat_rai_fun :: "rat \<Rightarrow> rai_intern \<Rightarrow> rai_intern" where
  "mult_rat_rai_fun x (Some y) = 
    (if x < 0 then uminus_rai_fun (Some (mult_rat_rai_fun_pos (-x) y))
      else if x = 0 then None else Some (mult_rat_rai_fun_pos x y))"
| "mult_rat_rai_fun x None = None"

private fun mult_rai_fun :: "rai_intern \<Rightarrow> rai_intern \<Rightarrow> rai_intern" where
  "mult_rai_fun (Some x) (Some y) = (case (x,y) of ((ri1,p1,l1,r1),(ri2,p2,l2,r2))
    \<Rightarrow> if r1 > 0 \<and> r2 > 0 then Some (mult_rai_fun_pos x y) else 
       if r1 > 0 \<and> r2 < 0 then 
         uminus_rai_fun (Some (mult_rai_fun_pos x (the (uminus_rai_fun (Some y))))) else
       if r1 < 0 \<and> r2 > 0 then
         uminus_rai_fun (Some (mult_rai_fun_pos (the (uminus_rai_fun (Some x))) y))
       else
         Some (mult_rai_fun_pos (the (uminus_rai_fun (Some x))) (the (uminus_rai_fun (Some y)))))"
| "mult_rai_fun None y = None"
| "mult_rai_fun x None = None"

lemma mult_rat_rai_fun_pos: fixes r1 :: rat assumes r1: "r1 > 0" and y: "rai_cond (Some y)"
  defines z: "z \<equiv> mult_rat_rai_fun_pos r1 y"
  shows "rai_cond (Some z) \<and> (rai_real (Some z) = of_rat r1 * rai_real (Some y))" 
proof -
  obtain ri2 p2 l2 r2 where yt: "y = (ri2,p2,l2,r2)" by (cases y, auto)
  let ?x = "real_of_rat r1"
  let ?y = "rai_real (Some ( ri2, p2, l2, r2))"
  let ?p = "poly_mult_rat r1 p2"    
  let ?mp = "monic_poly ?p"
  let ?ri = "count_roots_interval_rat ?mp"
  let ?lr = "root_info.l_r"
  note y = rai_condD[OF y[unfolded yt]]
  from y(5) r1 have p: "?p \<noteq> 0" and r10: "r1 \<noteq> 0" by auto
  hence mp: "?mp \<noteq> 0" by (simp add: monic_poly)
  from y(1)[unfolded root_cond_def split] 
  have rt: "rpoly p2 ?y = 0" and bnd: "of_rat l2 \<le> ?y" "?y \<le> of_rat r2" by auto
  from rt have rt: "rpoly ?mp (?x * ?y) = 0" unfolding monic_poly rpoly_mult_rat using r1
    by (simp add: field_simps)
  from poly_cond_D[OF y(10)] have "square_free p2" by simp
  hence sf: "square_free ?mp" unfolding monic_poly by (rule poly_mult_rat_square_free[OF r10])
  have mon: "monic ?mp" by (rule monic_poly(2)[OF p])
  note ri = count_roots_interval_rat[OF sf]
  obtain l r where lr: "l = l2 * r1" "r = r2 * r1" by force
  from bnd r1 have bnd: "of_rat l \<le> ?x * ?y" "?x * ?y \<le> of_rat r" unfolding lr of_rat_mult by auto
  with rt have rc: "root_cond (?mp,l,r) (?x * ?y)" unfolding root_cond_def by auto
  have ur: "unique_root (?mp,l,r)" unfolding unique_root_def
  proof (rule ex1I, rule rc)
    fix z
    assume "root_cond (?mp,l,r) z"
    from this[unfolded root_cond_def split] have bndz: "of_rat l \<le> z" "z \<le> of_rat r" 
      and rt: "rpoly ?mp z = 0" by auto
    from rt have rt: "rpoly p2 (z * inverse ?x) = 0" unfolding rpoly_mult_rat monic_poly .
    from bndz r1 have "of_rat l2 \<le> z * inverse ?x" "z * inverse ?x \<le> of_rat r2" unfolding lr of_rat_mult
      by (auto simp: field_simps)
    with rt have "root_cond (p2,l2,r2) (z * inverse ?x)" unfolding root_cond_def by auto
    from y(8)[OF this] have "?y = z * inverse ?x" by auto
    thus "z = ?x * ?y" using r1 by auto
  qed
  from r1 have sgnr: "sgn r = sgn r2" unfolding lr 
    by (cases "r2 = 0"; cases "r2 < 0"; auto simp: mult_neg_pos mult_less_0_iff)
  from r1 have sgnl: "sgn l = sgn l2" unfolding lr 
    by (cases "l2 = 0"; cases "l2 < 0"; auto simp: mult_neg_pos mult_less_0_iff)
  from the_unique_root(5)[OF ur rc] have xy: "?x * ?y = the_unique_root (?mp,l,r)" by auto
  from y(3) r1 xy have non0: "the_unique_root (?mp,l,r) \<noteq> 0" by auto
  from z[unfolded yt, simplified, unfolded Let_def lr[symmetric] split]
  have z: "z = ( ?ri, ?mp, l, r)" by simp
  have yp2: "alg_poly ?y p2" using y(1,5) unfolding root_cond_def split alg_poly_def by auto
  from poly_mult_rat_irreducible r1 poly_cond_D[OF y(10)] y(5) 
  have "irreducible ?mp"  "monic ?mp" by (auto simp: monic_poly(1-3))
  with mon sf have un: "poly_cond ?mp" by (auto simp: poly_cond_def)
  have rc: "rai_cond (Some z)" unfolding z using y(2,4) un
    by (simp add: rai_cond_def ur ri mp sgnr sgnl)
  thus ?thesis unfolding yt xy unfolding z by (simp add: rai_real_def)
qed

lemma mult_rai_fun_pos: assumes x: "rai_cond (Some x)" and y: "rai_cond (Some y)"
  defines z: "z \<equiv> mult_rai_fun_pos x y"
  assumes pos: "rai_real (Some x) > 0" "rai_real (Some y) > 0"
  shows "rai_cond (Some z) \<and> (rai_real (Some z) = rai_real (Some x) * rai_real (Some y))" 
proof -
  obtain ri1 p1 l1 r1 where xt: "x = (ri1,p1,l1,r1)" by (cases x, auto)
  obtain ri2 p2 l2 r2 where yt: "y = (ri2,p2,l2,r2)" by (cases y, auto)
  let ?x = "rai_real (Some ( ri1, p1, l1, r1))"
  let ?y = "rai_real (Some ( ri2, p2, l2, r2))"
  let ?r = "real_of_rat"
  let ?p1 = "normalize_rat_poly p1"
  let ?p2 = "normalize_rat_poly p2"
  let ?p = "poly_mult ?p1 ?p2"
  let ?lr = "root_info.l_r"
  note x = rai_condD[OF x[unfolded xt]]
  note y = rai_condD[OF y[unfolded yt]]
  from x(1,5) have ax: "alg_poly ?x ?p1" unfolding root_cond_def alg_poly_def by simp
  from y(1,5) have ay: "alg_poly ?y ?p2" unfolding root_cond_def alg_poly_def by simp
  from alg_poly_mult_real[OF ax ay] pos[unfolded xt yt] have axy: "alg_poly (?x * ?y) ?p" by auto
  from alg_polyD[OF this] have p: "?p \<noteq> 0" and rt: "rpoly ?p (?x * ?y) = 0" .
  from x(1) pos(1)[unfolded xt] have "?r r1 > 0" unfolding root_cond_def split by arith
  hence "sgn r1 = 1" unfolding sgn_rat_def by (auto split: if_splits)
  with x(2) have "sgn l1 = 1" by simp
  hence l1_pos: "l1 > 0" unfolding sgn_rat_def by (cases "l1 = 0"; cases "l1 < 0"; auto)
  from y(1) pos(2)[unfolded yt] have "?r r2 > 0" unfolding root_cond_def split by arith
  hence "sgn r2 = 1" unfolding sgn_rat_def by (auto split: if_splits)
  with y(2) have "sgn l2 = 1" by simp
  hence l2_pos: "l2 > 0" unfolding sgn_rat_def by (cases "l2 = 0"; cases "l2 < 0"; auto)
  let ?bnd = "(\<lambda>((l1, r1), l2 :: rat, r2 :: rat). (l1 * l2, r1 * r2))"
  def bnd \<equiv> ?bnd
  obtain z' where sel: "select_correct_factor_rat_poly
        (tighten_poly_bounds_binary (?lr ri1) (?lr ri2))
        bnd 
        ((l1, r1), l2, r2)
        (poly_mult (normalize_rat_poly p1) (normalize_rat_poly p2)) = z'" by auto
  have main: "rai_cond z' \<and> rai_real z' = ?x * ?y"
  proof (rule select_correct_factor_rat_poly[OF _ sel rt p])
    {
      fix l1 r1 l2 r2 l1' r1' l2' r2' l l' r r' :: rat
      let ?m1 = "(l1+r1)/2" let ?m2 = "(l2+r2)/2"
      def d1 \<equiv> "r1 - l1" def d2 \<equiv> "r2 - l2"
      let ?M1 = "l1 + d1/2" let ?M2 = "l2 + d2/2"
      assume le: "l1 > 0" "l2 > 0" "l1 \<le> r1" "l2 \<le> r2" and id: "(l, r) = (l1 * l2, r1 * r2)"
        "(l', r') = (l1' * l2', r1' * r2')" 
        and mem: "(l1', r1') \<in> {(l1, ?m1), (?m1, r1)}"
          "(l2', r2') \<in> {(l2, ?m2), (?m2, r2)}"
      hence id: "l = l1 * l2" "r = (l1 + d1) * (l2 + d2)" "l' = l1' * l2'" "r' = r1' * r2'" 
        "r1 = l1 + d1" "r2 = l2 + d2" and id': "?m1 = ?M1" "?m2 = ?M2"
        unfolding d1_def d2_def by (auto simp: field_simps)
      def l1d1 \<equiv> "l1 + d1"
      from le have ge0: "d1 \<ge> 0" "d2 \<ge> 0" "l1 \<ge> 0" "l2 \<ge> 0" unfolding d1_def d2_def by auto
      have "4 * (r' - l') \<le> 3 * (r - l)" 
      proof (cases "l1' = l1 \<and> r1' = ?M1 \<and> l2' = l2 \<and> r2' = ?M2")
        case True
        hence id2: "l1' = l1" "r1' = ?M1" "l2' = l2" "r2' = ?M2" by auto
        show ?thesis unfolding id id2 unfolding ring_distribs using ge0 by simp 
      next
        case False note 1 = this
        show ?thesis
        proof (cases "l1' = l1 \<and> r1' = ?M1 \<and> l2' = ?M2 \<and> r2' = r2")
          case True
          hence id2: "l1' = l1" "r1' = ?M1" "l2' = ?M2" "r2' = r2" by auto
          show ?thesis unfolding id id2 unfolding ring_distribs using ge0 by simp
        next
          case False note 2 = this
          show ?thesis
          proof (cases "l1' = ?M1 \<and> r1' = r1 \<and> l2' = l2 \<and> r2' = ?M2")
            case True
            hence id2: "l1' = ?M1" "r1' = r1" "l2' = l2" "r2' = ?M2" by auto
          show ?thesis unfolding id id2 unfolding ring_distribs using ge0 by simp
          next
            case False note 3 = this
            from 1 2 3 mem have id2: "l1' = ?M1" "r1' = r1" "l2' = ?M2" "r2' = r2"
              unfolding id' by auto
          show ?thesis unfolding id id2 unfolding ring_distribs using ge0 by simp
          qed
        qed
      qed
      hence "r' - l' \<le> 3 / 4 * (r - l)" by simp
    } note decr = this
    have tur: "?x = the_unique_root (p1,l1,r1)" "?y = the_unique_root (p2,l2,r2)"
      unfolding rai_real_def by auto
    show "converges_to
        (\<lambda>i. bnd ((tighten_poly_bounds_binary (root_info.l_r ri1) (root_info.l_r ri2) ^^ i)
        ((l1, r1), l2, r2))) (?x * ?y)"
    proof (rule tighten_poly_bounds_binary[OF x(9) refl y(9) refl x(7) y(7) tur, 
       where f = "op *" and I = "\<lambda> l. l > 0", OF _ _ _ l1_pos l2_pos], goal_cases)
      case (1 L1 R1 L2 R2 L R)
      hence "L = L1 * L2" "R = R1 * R2" unfolding bnd_def by auto
      hence id: "?r L = ?r L1 * ?r L2" "?r R = ?r R1 * ?r R2" by auto
      from 1(3-4) have le: "?r L1 \<le> ?x" "?x \<le> ?r R1" "?r L2 \<le> ?y" "?y \<le> ?r R2" 
        unfolding root_cond_def by auto
      from 1(1-2) have lt: "0 < ?r L1" "0 < ?r L2" by auto      
      from mult_mono[OF le(1,3), folded id] lt le have L: "?r L \<le> ?x * ?y" by auto
      have R: "?x * ?y \<le> ?r R"
        by (rule mult_mono[OF le(2,4), folded id], insert lt le, linarith+)
      show ?case using L R by blast
    next
      case (2 l1 r1 l2 r2 l1' r1' l2' r2' l l' r r')
      from 2(5-6) have lr: "l = l1 * l2" "r = r1 * r2" "l' = l1' * l2'" "r' = r1' * r2'"
        unfolding bnd_def by auto      
      from 2(1-4) have le: "0 < l1" "0 < l2" "l1 \<le> r1" "l2 \<le> r2" by auto
      from 2(7-8) le have le': "l1 \<le> l1'" "r1' \<le> r1" "l2 \<le> l2'" "r2' \<le> r2" "0 < r2'" "0 < r2" by auto
      from mult_mono[OF le'(1,3), folded lr] le le' have l: "l \<le> l'" by auto
      have r: "r' \<le> r" by (rule mult_mono[OF le'(2,4), folded lr], insert le le', linarith+)
      have "r' - l' \<le> 3 / 4 * (r - l)"
        by (rule decr[OF _ _ _ _ _ _ 2(7-8)], insert le le' lr, auto)
      thus ?case using l r by blast
    qed auto
  qed
  with pos xt yt obtain z'' where z': "z' = Some z''" by (cases z', auto)
  have z': "z' = Some z" unfolding z[unfolded xt yt, simplified, unfolded bnd_def[symmetric] sel z']
    using z' by auto
  from main[unfolded this] show ?thesis unfolding xt yt by simp
qed

lemma rai_cond_pos: assumes "rai_cond (Some (ri,p,l,r))"
  shows "rai_real (Some (ri,p,l,r)) > 0 \<longleftrightarrow> r > 0"
   "rai_real (Some (ri,p,l,r)) < 0 \<longleftrightarrow> r < 0"
proof -
  let ?r = "real_of_rat"
  let ?x = "rai_real (Some (ri,p,l,r))"
  from assms[unfolded rai_cond_def]
  have ur: "unique_root (p,l,r)" and sgn: "sgn l = sgn r" "sgn r \<noteq> 0" by auto
  from the_unique_root(1-2)[OF ur] have le: "?r l \<le> ?x" "?x \<le> ?r r" unfolding rai_real_def by auto
  have "(?x > 0 \<longleftrightarrow> r > 0) \<and> (?x < 0 \<longleftrightarrow> r < 0)"
  proof (cases "r > 0")
    case True
    with sgn have "sgn l = 1" by simp
    hence "l > 0" unfolding sgn_rat_def by (cases "l = 0"; cases "l < 0"; auto)
    hence "?r l > 0" by auto
    hence "?x > 0" using le(1) by arith
    with True show ?thesis by auto
  next
    case False
    with sgn(2) have r: "r < 0" unfolding sgn_rat_def by (cases "r = 0"; auto)
    hence "?r r < 0" by auto
    with le(2) have "?x < 0" by arith
    with r show ?thesis by auto
  qed
  thus "?x > 0 \<longleftrightarrow> r > 0" "?x < 0 \<longleftrightarrow> r < 0" by blast+
qed

lemma negate_the_uminus_rai_fun: assumes "rai_cond (Some x)"
  shows "rai_cond (Some (the (uminus_rai_fun (Some x)))) \<and> rai_real (Some (the (uminus_rai_fun (Some x))))
    = - rai_real (Some x)"
  using uminus_rai_main[OF assms] unfolding uminus_rai_fun_def by auto

lemma mult_rai_main: assumes x: "rai_cond x" and y: "rai_cond y"
  defines z: "z \<equiv> mult_rai_fun x y"
  shows "rai_cond z \<and> (rai_real z = rai_real x * rai_real y)" 
proof (cases x)
  case None
  with y show ?thesis unfolding z by simp
next
  case (Some xt) note xt = this
  show ?thesis
  proof (cases y)
    case None
    with x y show ?thesis unfolding z xt by simp
  next
    case (Some yt) note yt = this
    obtain ri1 p1 l1 r1 where xt: "x = Some (ri1,p1,l1,r1)" unfolding xt by (cases xt, auto)
    obtain ri2 p2 l2 r2 where yt: "y = Some (ri2,p2,l2,r2)" unfolding yt by (cases yt, auto)
    let ?xt = "( ri1, p1, l1, r1)"
    let ?yt = "( ri2, p2, l2, r2)"
    let ?x = "rai_real (Some ?xt)"
    let ?y = "rai_real (Some ?yt)"
    let ?mxt = "the (uminus_rai_fun (Some ?xt))"
    let ?myt = "the (uminus_rai_fun (Some ?yt))"
    let ?mx = "rai_real (Some ?mxt)"
    let ?my = "rai_real (Some ?myt)"
    let ?r = "real_of_rat"
    note x = x[unfolded xt]
    note y = y[unfolded yt]
    from negate_the_uminus_rai_fun[OF x] have mx: "rai_cond (Some ?mxt)" and [simp]: "?mx = - ?x" by auto
    from negate_the_uminus_rai_fun[OF y] have my: "rai_cond (Some ?myt)" and [simp]: "?my = - ?y" by auto
    have id: "r1 > 0 \<longleftrightarrow> ?x > 0" "r1 < 0 \<longleftrightarrow> ?x < 0" "r2 > 0 \<longleftrightarrow> ?y > 0" "r2 < 0 \<longleftrightarrow> ?y < 0" 
      unfolding rai_cond_pos[OF x] rai_cond_pos[OF y] by auto
    note z = z[unfolded xt yt mult_rai_fun.simps split id]
    show ?thesis
    proof (cases "?x > 0 \<and> ?y > 0")
      case True
      with z have z: "z = Some (mult_rai_fun_pos ?xt ?yt)" by simp
      from mult_rai_fun_pos[OF x y] True 
      show ?thesis unfolding xt yt z by auto
    next
      case False note pp = this
      hence "(?x > 0 \<and> ?y > 0) = False" by simp
      note z = z[unfolded this if_False]
      show ?thesis
      proof (cases "?x > 0 \<and> ?y < 0")
        case True
        with z have z: "z = uminus_rai_fun (Some (mult_rai_fun_pos ?xt ?myt))" by simp        
        from True have pos: "?x > 0" "?my > 0" by auto
        from mult_rai_fun_pos[OF x my pos]
        show ?thesis unfolding z xt yt using uminus_rai_main[of "Some (mult_rai_fun_pos ?xt ?myt)"]
          by auto
      next
        case False note pn = this
        hence "(?x > 0 \<and> ?y < 0) = False" by simp
        note z = z[unfolded this if_False]
        show ?thesis
        proof (cases "?x < 0 \<and> ?y > 0")
          case True
          with z have z: "z = uminus_rai_fun (Some (mult_rai_fun_pos ?mxt ?yt))" by simp        
          from True have pos: "?mx > 0" "?y > 0" by auto
          from mult_rai_fun_pos[OF mx y pos]
          show ?thesis unfolding z xt yt using uminus_rai_main[of "Some (mult_rai_fun_pos ?mxt ?yt)"]
            by auto
        next
          case False note np = this
          with z have z: "z = Some (mult_rai_fun_pos ?mxt ?myt)" by simp
          from rai_condD(3)[OF x] rai_condD(3)[OF y]
          have "?x \<noteq> 0" "?y \<noteq> 0" by auto
          with pp np pn have "?x < 0" "?y < 0" by arith+
          hence "?mx > 0" "?my > 0" by auto
          from mult_rai_fun_pos[OF mx my this]
          show ?thesis unfolding xt yt z by auto
        qed
      qed
    qed
  qed
qed

lemma mult_rat_rai_main: fixes x assumes y: "rai_cond y"
  defines z: "z \<equiv> mult_rat_rai_fun x y"
  shows "rai_cond z \<and> (rai_real z = of_rat x * rai_real y)" 
proof (cases "x = 0 \<or> y = None")
  case True
  show ?thesis unfolding z using True by (cases y, auto)
next
  case False
  then obtain yt where x: "(x = 0) = False" and yt: "y = Some yt" by (cases y, auto)
  obtain ri2 p2 l2 r2 where yt: "y = Some (ri2,p2,l2,r2)" unfolding yt by (cases yt, auto)
  let ?yt = "( ri2, p2, l2, r2)"
  let ?x = "real_of_rat x"
  let ?y = "rai_real (Some ?yt)"
  let ?myt = "mult_rat_rai_fun_pos (- x) ( ri2, p2, l2, r2)"
  note y = y[unfolded yt]
  note z = z[unfolded yt mult_rat_rai_fun.simps split x if_False]
  show ?thesis
  proof (cases "x < 0")
    case False
    with x have x: "x > 0" by auto
    with z have z: "z = Some (mult_rat_rai_fun_pos x ?yt)" by simp
    from mult_rat_rai_fun_pos[OF x y] 
    show ?thesis unfolding yt z by auto
  next
    case True 
    with x have x: "- x > 0" by auto
    hence z: "z = uminus_rai_fun (Some ?myt)" unfolding z by simp
    from mult_rat_rai_fun_pos[OF x y] have rc: "rai_cond (Some ?myt)" 
      and rr: "rai_real (Some ?myt) = - ?x * ?y" by auto
    from uminus_rai_main[OF rc] rr show ?thesis unfolding z[symmetric] unfolding yt[symmetric]
      by simp
  qed
qed

lift_definition mult_rai :: "real_alg_intern \<Rightarrow> real_alg_intern \<Rightarrow> real_alg_intern" is mult_rai_fun
  by (insert mult_rai_main, auto)
  
lemma mult_rai: "real_of_rai (mult_rai x y) = real_of_rai x * real_of_rai y"
  by (transfer, insert mult_rai_main, auto)

lift_definition mult_rat_rai :: "rat \<Rightarrow> real_alg_intern \<Rightarrow> real_alg_intern" is mult_rat_rai_fun
  by (insert mult_rat_rai_main, auto)
  
lemma mult_rat_rai: "real_of_rai (mult_rat_rai x y) = of_rat x * real_of_rai y"
  by (transfer, insert mult_rat_rai_main, auto)
end

(* **************************************************************** *)
subsection \<open>Real Algebraic Numbers = Rational + Irrational Real Algebraic Numbers\<close>

text \<open>In the next representation of real algebraic numbers, we distinguish between
  rational and irrational numbers. The advantage is that whenever we only work on
  rational numbers, there is not much overhead involved in comparison to the 
  existing implementation of real numbers which just supports the rational numbers.\<close>

subsubsection \<open>Definitions and Algorithms on Raw Type\<close>
datatype real_alg_dt = Rational rat | Irrational real_alg_intern

fun radt_cond :: "real_alg_dt \<Rightarrow> bool" where 
  "radt_cond (Irrational rai) = (degree (fst (info_rai rai)) \<ge> 2)"
| "radt_cond (Rational r) = True"
  
fun rai_of_radt :: "real_alg_dt \<Rightarrow> real_alg_intern" where
  "rai_of_radt (Rational r) = of_rat_rai r"
| "rai_of_radt (Irrational rai) = rai"

fun real_of_radt :: "real_alg_dt \<Rightarrow> real" where
  "real_of_radt (Rational r) = of_rat r"
| "real_of_radt (Irrational rai) = real_of_rai rai"

definition real_alg_dt :: "real_alg_intern \<Rightarrow> real_alg_dt" where 
  "real_alg_dt rai \<equiv> let rai' = normalize_bounds_rai rai; 
     (p,n) = info_rai rai'
     in (if degree p = 1 then Rational (- coeff p 0)
       else Irrational rai')"

lemma real_alg_dt_code[code]: "real_alg_dt rai = (let rai' = normalize_bounds_rai rai; 
     p = poly_rai rai'
     in (if degree p = 1 then Rational (- coeff p 0)
       else Irrational rai'))"
  by (auto simp: poly_rai_info_rai real_alg_dt_def Let_def split: prod.splits)
  
  
lemma rai_of_radt: "real_of_rai (rai_of_radt x) = real_of_radt x"
  by (cases x, auto simp: of_rat_rai)

lemma real_alg_dt: "radt_cond (real_alg_dt rai)" "real_of_radt (real_alg_dt rai) = real_of_rai rai"
proof -
  def rai' \<equiv> "normalize_bounds_rai rai"
  obtain p n where ri: "info_rai rai' = (p,n)" by force
  have rai': "real_of_rai rai = real_of_rai rai'" unfolding rai'_def by simp
  have id: "real_alg_dt rai = (if degree p = 1 then Rational (- coeff p 0)
    else Irrational rai')" unfolding real_alg_dt_def Let_def
      using rai'_def ri by auto
  from rai_info_poly[OF ri[unfolded rai'_def]]
  have p: "monic p" "rpoly p (real_of_rai rai') = 0" 
    "degree p \<ge> 1" by (auto simp: rai')
  have "radt_cond (real_alg_dt rai) \<and> real_of_radt (real_alg_dt rai) = real_of_rai rai"
  proof (cases "degree p = 1")
    case True
    hence id: "real_alg_dt rai = Rational (- coeff p 0)" unfolding id by simp
    from True p(1) have "[: coeff p 0, 1 :] = p"
      by (metis One_nat_def coeff_pCons_0 coeff_pCons_Suc degree1_coeffs)
    with p(2) have "rpoly [: coeff p 0, 1 :] (real_of_rai rai') = 0" by auto
    from this[unfolded eval_poly_def] have id': "real_of_rai rai' = of_rat (- coeff p 0)" by simp    
    show ?thesis unfolding id rai' id' by auto
  next
    case False
    hence id: "real_alg_dt rai = Irrational rai'" unfolding id by simp
    show ?thesis unfolding id rai' using ri p False
      by auto
  qed
  thus "radt_cond (real_alg_dt rai)" "real_of_radt (real_alg_dt rai) = real_of_rai rai" by auto
qed

definition add_rat_radt :: "rat \<Rightarrow> real_alg_dt \<Rightarrow> real_alg_intern" where
  "add_rat_radt x y = (add_rat_rai x (rai_of_radt y))"

definition plus_rat_radt :: "rat \<Rightarrow> real_alg_dt \<Rightarrow> real_alg_dt" where
  "plus_rat_radt x y = real_alg_dt (add_rat_radt x y)"

lemma add_rat_radt: "real_of_rai (add_rat_radt x y) = of_rat x + real_of_radt y"
  unfolding add_rat_radt_def by (auto simp: add_rat_rai of_rat_rai rai_of_radt)

lemma plus_rat_radt: "real_of_radt (plus_rat_radt x y) = of_rat x + real_of_radt y"
  "radt_cond (plus_rat_radt x y)"
  unfolding plus_rat_radt_def by (auto simp: real_alg_dt add_rat_radt)

definition mult_rat_radt :: "rat \<Rightarrow> real_alg_dt \<Rightarrow> real_alg_dt" where
  "mult_rat_radt x y = real_alg_dt (mult_rat_rai x (rai_of_radt y))"

lemma mult_rat_radt: "real_of_radt (mult_rat_radt x y) = of_rat x * real_of_radt y"
  "radt_cond (mult_rat_radt x y)"
  unfolding mult_rat_radt_def by (auto simp: real_alg_dt mult_rat_rai rai_of_radt)

definition of_rat_radt :: "rat \<Rightarrow> real_alg_dt" where
  [code_unfold]: "of_rat_radt = Rational"

lemma of_rat_radt: "real_of_radt (of_rat_radt x) = of_rat x" "radt_cond (of_rat_radt x)"
  by (auto simp: of_rat_radt_def)

fun uminus_radt :: "real_alg_dt \<Rightarrow> real_alg_dt" where
  "uminus_radt (Rational r) = Rational (-r)"
| "uminus_radt x = real_alg_dt (uminus_rai (rai_of_radt x))"

lemma uminus_radt: "real_of_radt (uminus_radt x) = uminus (real_of_radt x)"
  "radt_cond (uminus_radt x)"
  by (cases x, auto simp: real_alg_dt uminus_rai)+

fun inverse_radt :: "real_alg_dt \<Rightarrow> real_alg_dt" where
  "inverse_radt (Rational r) = Rational (inverse r)"
| "inverse_radt x = real_alg_dt (inverse_rai (rai_of_radt x))"

lemma inverse_radt: "real_of_radt (inverse_radt x) = inverse (real_of_radt x)"
  "radt_cond (inverse_radt x)"
  by (cases x, auto simp: real_alg_dt inverse_rai)+

definition root_radt :: "nat \<Rightarrow> real_alg_dt \<Rightarrow> real_alg_dt" where
  "root_radt n x = real_alg_dt (root_rai n (rai_of_radt x))"

lemma root_radt: "real_of_radt (root_radt n x) = root n (real_of_radt x)"
  "radt_cond (root_radt n x)"
  by (auto simp: real_alg_dt root_radt_def root_rai rai_of_radt)+

fun add_radt :: "real_alg_dt \<Rightarrow> real_alg_dt \<Rightarrow> real_alg_intern" where
  "add_radt (Rational r) (Rational q) = of_rat_rai (r + q)"
| "add_radt (Rational r) x = add_rat_radt r x"
| "add_radt x (Rational q) = add_rat_radt q x"
| "add_radt x y = (add_rai (rai_of_radt x) (rai_of_radt y))"

fun plus_radt :: "real_alg_dt \<Rightarrow> real_alg_dt \<Rightarrow> real_alg_dt" where
  "plus_radt (Rational r) (Rational q) = Rational (r + q)"
| "plus_radt (Rational r) x = plus_rat_radt r x"
| "plus_radt x (Rational q) = plus_rat_radt q x"
| "plus_radt x y = real_alg_dt (add_rai (rai_of_radt x) (rai_of_radt y))"

lemma add_radt: "real_of_rai (add_radt x y) = real_of_radt x + real_of_radt y"
  by (cases x; cases y; auto simp: add_rat_radt of_rat_rai add_rai)+

lemma plus_radt: "real_of_radt (plus_radt x y) = real_of_radt x + real_of_radt y"
  "radt_cond (plus_radt x y)"
  by (cases x; cases y; auto simp: plus_rat_radt real_alg_dt add_rai)+

fun mult_radt :: "real_alg_dt \<Rightarrow> real_alg_dt \<Rightarrow> real_alg_dt" where
  "mult_radt (Rational r) (Rational q) = Rational (r * q)"
| "mult_radt (Rational r) x = mult_rat_radt r x"
| "mult_radt x (Rational q) = mult_rat_radt q x"
| "mult_radt x y = real_alg_dt (mult_rai (rai_of_radt x) (rai_of_radt y))"

lemma mult_radt: "real_of_radt (mult_radt x y) = real_of_radt x * real_of_radt y"
  "radt_cond (mult_radt x y)"
  by (cases x; cases y; auto simp: mult_rat_radt real_alg_dt mult_rai)+

lemma rational_root_free_degree_iff: assumes rf: "root_free p" and rt: "rpoly p x = 0"
  shows "(x \<in> \<rat>) = (degree p = 1)"
proof 
  assume "x \<in> \<rat>"
  then obtain y where x: "x = of_rat y" (is "_ = ?x") unfolding Rats_def by blast
  from rt x have "poly p y = 0" by (simp add: rpoly.eval_poly_poly)
  with rf show "degree p = 1" unfolding root_free_def by auto
next
  assume "degree p = 1"
  from degree1_coeffs[OF this]
  obtain a b where p: "p = [:a,b:]" and b: "b \<noteq> 0" by auto
  from rt[unfolded p] have "of_rat a + x * of_rat b = 0"
    by (auto simp: eval_poly_def)
  from arg_cong[OF this, of "\<lambda> x. (x - of_rat a) / of_rat b"]
  have "x = - of_rat a / of_rat b" using b by auto
  also have "\<dots> = of_rat (- a / b)" unfolding of_rat_minus of_rat_divide ..
  finally show "x \<in> \<rat>" by auto
qed

fun to_rat_radt :: "real_alg_dt \<Rightarrow> rat option" where
  "to_rat_radt (Rational r) = Some r"
| "to_rat_radt (Irrational rai) = None"

lemma to_rat_radt: assumes rc: "radt_cond x" 
  shows "to_rat_radt x = (if real_of_radt x \<in> \<rat> then Some (THE q. real_of_radt x = of_rat q) else None)"
proof (cases x)
  case (Irrational rai)
  let ?x = "real_of_rai rai"
  obtain p n where ir: "info_rai rai = (p,n)" by force
  from rai_info_poly[OF this] 
  have rf: "poly_cond p"
    and rt: "rpoly p ?x = 0" by auto
  from rc[unfolded Irrational] ir have deg: "degree p \<noteq> 1" by auto
  from poly_cond_D[OF rf] have rf: "root_free p" and mon: "monic p" by auto
  show ?thesis using deg rational_root_free_degree_iff[OF rf rt] unfolding Irrational
    by (simp add: ir)
qed simp

fun equal_radt :: "real_alg_dt \<Rightarrow> real_alg_dt \<Rightarrow> bool" where
  "equal_radt (Rational r) (Rational q) = (r = q)" 
| "equal_radt (Irrational xx) (Irrational yy) = (eq_rai xx yy)"
| "equal_radt (Rational r) (Irrational yy) = False"
| "equal_radt (Irrational xx) (Rational q) = False"

lemma equal_radt[simp]: assumes rc: "radt_cond x" "radt_cond y" 
  shows "equal_radt x y = (real_of_radt x = real_of_radt y)"
proof (cases x)
  case (Rational r) note xx = this
  show ?thesis
  proof (cases y)
    case (Rational q) note yy = this
    show ?thesis unfolding xx yy by simp
  next
    case (Irrational yy) note yy = this
    {
      assume "real_of_rat r = real_of_rai yy" 
      from arg_cong[OF this, of "\<lambda> x. x \<in> \<rat>"]
        to_rat_radt[OF rc(2)] have False unfolding xx yy by auto
    }
    thus ?thesis unfolding xx yy by auto
  qed
next
  case (Irrational xx) note xx = this
  show ?thesis
  proof (cases y)
    case (Rational q) note yy = this
    {
      assume "real_of_rat q = real_of_rai xx" 
      from arg_cong[OF this, of "\<lambda> x. x \<in> \<rat>"]
        to_rat_radt[OF rc(1)] have False unfolding xx yy by auto
    }
    thus ?thesis unfolding xx yy by auto
  next
    case (Irrational yy) note yy = this
    from eq_rai[of xx yy]
    show ?thesis unfolding xx yy by simp
  qed
qed

fun compare_radt :: "real_alg_dt \<Rightarrow> real_alg_dt \<Rightarrow> order" where 
  "compare_radt (Rational r) (Rational q) = (compare r q)"
| "compare_radt (Irrational xx) (Irrational yy) = (compare_rai xx yy)"
| "compare_radt (Rational r) (Irrational xx) = (compare_rat_rai r xx)"
| "compare_radt (Irrational xx) (Rational r) = (invert_order (compare_rat_rai r xx))"

lemma compare_radt: assumes rc: "radt_cond x" "radt_cond y"
  shows "compare_radt x y = compare (real_of_radt x) (real_of_radt y)"
proof (cases x)
  case (Rational r) note xx = this
  show ?thesis
  proof (cases y)
    case (Rational q) note yy = this
    show ?thesis unfolding xx yy by (simp add: compare_rat_def compare_real_def comparator_of_def of_rat_less)
  next
    case (Irrational yy) note yy = this
    have "real_of_rat r \<noteq> real_of_rai yy" using equal_radt[OF assms] unfolding xx yy by auto
    from compare_rat_rai[OF this]
    show ?thesis unfolding xx yy by (simp add: of_rat_rai)
  qed
next
  case (Irrational xx) note xx = this
  show ?thesis
  proof (cases y)
    case (Rational q) note yy = this
    have "real_of_rat q \<noteq> real_of_rai xx" using equal_radt[OF assms] unfolding xx yy by auto
    from compare_rat_rai[OF this]
    show ?thesis unfolding xx yy by simp
  next
    case (Irrational yy) note yy = this
    from compare_rai[of xx yy]
    show ?thesis unfolding xx yy by (simp add: compare_rai)
  qed
qed

fun sgn_radt :: "real_alg_dt \<Rightarrow> rat" where
  "sgn_radt (Rational r) = sgn r"
| "sgn_radt (Irrational rai) = sgn_rai rai"

lemma sgn_radt: "radt_cond x \<Longrightarrow> real_of_rat (sgn_radt x) = sgn (real_of_radt x)" 
  using sgn_rai by (cases x, auto simp: real_of_rat_sgn)

lemma normalize_bounds_rai_of_rat_rai: "normalize_bounds_rai (of_rat_rai r) = of_rat_rai r"
proof (transfer)
  fix r
  show "rai_normalize_bounds (of_rat_rai_fun r) = of_rat_rai_fun r"
    by (auto simp add: rai_normalize_bounds_def of_rat_rai_fun_def rai_normalize_poly_flat_def 
    rai_normalize_bounds_flat_def real_alg_precision_def tighten_poly_bounds_epsilon.simps Let_def
    poly_rat_def tighten_poly_bounds_for_x.simps)
qed

fun floor_radt :: "real_alg_dt \<Rightarrow> int" where
  "floor_radt (Rational r) = floor r"
| "floor_radt (Irrational rai) = floor_rai rai"

lemma floor_radt: "floor_radt x = floor (real_of_radt x)"
  by (cases x, auto simp: floor_rai)
  
(* *************** *)
subsubsection \<open>Definitions and Algorithms on Type with Invariant\<close>

typedef real_alg_dtc = "Collect radt_cond" by (rule exI[of _ "Rational 0"], auto)

setup_lifting type_definition_real_alg_dtc

lift_definition real_of_radtc :: "real_alg_dtc \<Rightarrow> real" is real_of_radt .

lift_definition of_rat_radtc :: "rat \<Rightarrow> real_alg_dtc" is of_rat_radt
  by (auto simp: of_rat_radt)

lemma of_rat_radtc: "real_of_radtc (of_rat_radtc x) = of_rat x"
  by (transfer, auto simp: of_rat_radt)

lift_definition radtc_of_rai :: "real_alg_intern \<Rightarrow> real_alg_dtc" is real_alg_dt
  by (insert real_alg_dt, auto)

lemma radtc_of_rai[simp]: "real_of_radtc (radtc_of_rai x) = real_of_rai x"
  by (transfer, insert real_alg_dt, auto)

lift_definition uminus_radtc :: "real_alg_dtc \<Rightarrow> real_alg_dtc" is uminus_radt 
  by (auto simp: uminus_radt)

lemma uminus_radtc: "real_of_radtc (uminus_radtc x) = - real_of_radtc x"
  by (transfer, auto simp: uminus_radt)

lift_definition inverse_radtc :: "real_alg_dtc \<Rightarrow> real_alg_dtc" is inverse_radt 
  by (auto simp: inverse_radt)

lemma inverse_radtc: "real_of_radtc (inverse_radtc x) = inverse (real_of_radtc x)"
  by (transfer, auto simp: inverse_radt)

lift_definition root_radtc :: "nat \<Rightarrow> real_alg_dtc \<Rightarrow> real_alg_dtc" is root_radt 
  by (auto simp: root_radt)

lemma root_radtc: "real_of_radtc (root_radtc n x) = root n (real_of_radtc x)"
  by (transfer, auto simp: root_radt)


lift_definition equal_radtc :: "real_alg_dtc \<Rightarrow> real_alg_dtc \<Rightarrow> bool" is equal_radt .

lemma equal_radtc: "equal_radtc x y = (real_of_radtc x = real_of_radtc y)"
  by (transfer, auto)  

lift_definition compare_radtc :: "real_alg_dtc \<Rightarrow> real_alg_dtc \<Rightarrow> order" is compare_radt .

lemma compare_radtc: "compare_radtc x y = (compare (real_of_radtc x) (real_of_radtc y))"
  by (transfer, auto simp: compare_radt)  

lift_definition plus_radtc :: "real_alg_dtc \<Rightarrow> real_alg_dtc \<Rightarrow> real_alg_dtc" is plus_radt 
  by (auto simp: plus_radt)

lemma plus_radtc: "real_of_radtc (plus_radtc x y) = real_of_radtc x + real_of_radtc y"
  by (transfer, auto simp: plus_radt)

lift_definition mult_radtc :: "real_alg_dtc \<Rightarrow> real_alg_dtc \<Rightarrow> real_alg_dtc" is mult_radt 
  by (auto simp: mult_radt)

lemma mult_radtc: "real_of_radtc (mult_radtc x y) = real_of_radtc x * real_of_radtc y"
  by (transfer, auto simp: mult_radt)

lift_definition sgn_radtc :: "real_alg_dtc \<Rightarrow> rat" is sgn_radt . 

lemma sgn_radtc: "real_of_rat (sgn_radtc x) = sgn (real_of_radtc x)" 
  by (transfer, auto simp: sgn_radt)

lift_definition to_rat_radtc :: "real_alg_dtc \<Rightarrow> rat option" is to_rat_radt .

lemma to_rat_radtc: "to_rat_radtc x = 
  (if real_of_radtc x \<in> \<rat> then Some (THE q. real_of_radtc x = of_rat q) else None)"
  by (transfer, simp add: to_rat_radt)

lift_definition floor_radtc :: "real_alg_dtc \<Rightarrow> int" is floor_radt .

lemma floor_radtc: "floor_radtc x = floor (real_of_radtc x)"
  by (transfer, auto simp: floor_radt)

(* *************** *)
subsubsection \<open>Definitions and Algorithms on Quotient Type\<close>

quotient_type real_alg = real_alg_dtc / "\<lambda> x y. real_of_radtc x = real_of_radtc y"
  morphisms rep_real_alg abstr_real_alg
  by (auto simp: equivp_def) metis


(* real_of *)
lift_definition real_of :: "real_alg \<Rightarrow> real" is real_of_radtc .

lemma real_of_inj: "(real_of x = real_of y) = (x = y)"
  by (transfer, simp)

(* uminus *)
instantiation real_alg :: uminus
begin
lift_definition uminus_real_alg :: "real_alg \<Rightarrow> real_alg" is uminus_radtc
  by (simp add: uminus_radtc)
instance ..
end

lemma uminus_real_alg: "- (real_of x) = real_of (- x)"
  by (transfer, rule uminus_radtc[symmetric])

(* add *)
instantiation real_alg :: plus
begin
lift_definition plus_real_alg :: "real_alg \<Rightarrow> real_alg \<Rightarrow> real_alg" is plus_radtc
  by (simp add: plus_radtc)
instance ..
end

lemma plus_real_alg: "(real_of x) + (real_of y) = real_of (x + y)"
  by (transfer, rule plus_radtc[symmetric])

(* minus *)
instantiation real_alg :: minus
begin
definition minus_real_alg :: "real_alg \<Rightarrow> real_alg \<Rightarrow> real_alg" where
  "minus_real_alg x y = x + (-y)"
instance ..
end

lemma minus_real_alg: "(real_of x) - (real_of y) = real_of (x - y)"
  unfolding minus_real_alg_def minus_real_def uminus_real_alg plus_real_alg  ..  

(* of_rat *)
lift_definition of_rat_real_alg :: "rat \<Rightarrow> real_alg" is of_rat_radtc .

lemma of_rat_real_alg: "real_of_rat x = real_of (of_rat_real_alg x)"
  by (transfer, rule of_rat_radtc[symmetric])

(* zero *)
instantiation real_alg :: zero
begin
definition zero_real_alg :: "real_alg" where "zero_real_alg \<equiv> of_rat_real_alg 0"
instance ..
end

lemma zero_real_alg: "0 = real_of 0"
  unfolding zero_real_alg_def by (simp add: of_rat_real_alg[symmetric])

(* one *)
instantiation real_alg :: one
begin
definition one_real_alg :: "real_alg" where "one_real_alg \<equiv> of_rat_real_alg 1"
instance ..
end

lemma one_real_alg: "1 = real_of 1"
  unfolding one_real_alg_def by (simp add: of_rat_real_alg[symmetric])

(* times *)
instantiation real_alg :: times
begin
lift_definition times_real_alg :: "real_alg \<Rightarrow> real_alg \<Rightarrow> real_alg" is mult_radtc
  by (simp add: mult_radtc)
instance ..
end

lemma times_real_alg: "(real_of x) * (real_of y) = real_of (x * y)"
  by (transfer, rule mult_radtc[symmetric])

(* inverse *)
instantiation real_alg :: inverse
begin
lift_definition inverse_real_alg :: "real_alg \<Rightarrow> real_alg" is inverse_radtc
  by (simp add: inverse_radtc)
definition divide_real_alg :: "real_alg \<Rightarrow> real_alg \<Rightarrow> real_alg" where
  "divide_real_alg x y = x * inverse y"
instance ..
end

lemma inverse_real_alg: "inverse (real_of x) = real_of (inverse x)"
  by (transfer, rule inverse_radtc[symmetric])

lemma divide_real_alg: "(real_of x) / (real_of y) = real_of (x / y)"
  unfolding divide_real_alg_def times_real_alg[symmetric] divide_real_def inverse_real_alg ..

(* group *)
instance real_alg :: ab_group_add
  apply intro_classes
  apply (transfer, unfold plus_radtc, force)
  apply (unfold zero_real_alg_def, transfer, unfold plus_radtc of_rat_radtc, force)
  apply (transfer, unfold plus_radtc of_rat_radtc, force)
  apply (transfer, unfold plus_radtc uminus_radtc of_rat_radtc, force)
  apply (unfold minus_real_alg_def, force)
done

(* field *)
instance real_alg :: field
  apply intro_classes
  apply (transfer, unfold mult_radtc, force)
  apply (transfer, unfold mult_radtc, force)
  apply (unfold one_real_alg_def, transfer, unfold mult_radtc of_rat_radtc, force)
  apply (transfer, unfold mult_radtc plus_radtc, force simp: field_simps)
  apply (unfold zero_real_alg_def, transfer, unfold of_rat_radtc, force)
  apply (transfer, unfold mult_radtc inverse_radtc of_rat_radtc, force simp: field_simps)
  apply (unfold divide_real_alg_def, force)
  apply (transfer, unfold inverse_radtc of_rat_radtc, force)
done

(* numeral *)
instance real_alg :: numeral ..  

(* root *)
lift_definition root_real_alg :: "nat \<Rightarrow> real_alg \<Rightarrow> real_alg" is root_radtc
  by (simp add: root_radtc)

lemma root_real_alg: "root n (real_of x) = real_of (root_real_alg n x)"
  by (transfer, rule root_radtc[symmetric])

(* sgn *)
lift_definition sgn_real_alg_rat :: "real_alg \<Rightarrow> rat" is sgn_radtc
  by (insert sgn_radtc, metis to_rat_of_rat)

lemma sgn_real_alg_rat: "real_of_rat (sgn_real_alg_rat x) = sgn (real_of x)" 
  by (transfer, auto simp: sgn_radtc)

instantiation real_alg :: sgn
begin
definition sgn_real_alg :: "real_alg \<Rightarrow> real_alg" where
  "sgn_real_alg x = of_rat_real_alg (sgn_real_alg_rat x)"
instance ..
end

lemma sgn_real_alg: "sgn (real_of x) = real_of (sgn x)"
  unfolding sgn_real_alg_def of_rat_real_alg[symmetric]
  by (transfer, simp add: sgn_radtc)

(* equal *)
instantiation real_alg :: equal
begin
lift_definition equal_real_alg :: "real_alg \<Rightarrow> real_alg \<Rightarrow> bool" is equal_radtc 
  by (simp add: equal_radtc)
instance 
proof
  fix x y :: real_alg
  show "equal_class.equal x y = (x = y)"
    by (transfer, simp add: equal_radtc)
qed
end

lemma equal_real_alg: "HOL.equal (real_of x) (real_of y) = (x = y)"
  unfolding equal_real_def by (transfer, auto)

(* comparisons *)
instantiation real_alg :: ord 
begin

definition less_real_alg :: "real_alg \<Rightarrow> real_alg \<Rightarrow> bool" where
  [code del]: "less_real_alg x y = (real_of x < real_of y)"

definition less_eq_real_alg :: "real_alg \<Rightarrow> real_alg \<Rightarrow> bool" where
  [code del]: "less_eq_real_alg x y = (real_of x \<le> real_of y)"

instance ..
end    

lemma less_real_alg: "less (real_of x) (real_of y) = (x < y)" unfolding less_real_alg_def ..
lemma less_eq_real_alg: "less_eq (real_of x) (real_of y) = (x \<le> y)" unfolding less_eq_real_alg_def ..

instantiation real_alg :: compare_order
begin

lift_definition compare_real_alg :: "real_alg \<Rightarrow> real_alg \<Rightarrow> order" is compare_radtc
  by (simp add: compare_radtc)

lemma compare_real_alg: "compare (real_of x) (real_of y) = (compare x y)"
  by (transfer, simp add: compare_radtc)

instance
proof (intro_classes, unfold compare_real_alg[symmetric, abs_def])
  show "le_of_comp (\<lambda>x y. compare (real_of x) (real_of y)) = op \<le>" 
    by (intro ext, auto simp: compare_real_def comparator_of_def le_of_comp_def less_eq_real_alg_def)
  show "lt_of_comp (\<lambda>x y. compare (real_of x) (real_of y)) = op <"
    by (intro ext, auto simp: compare_real_def comparator_of_def lt_of_comp_def less_real_alg_def)
  show "comparator (\<lambda>x y. compare (real_of x) (real_of y))" 
    unfolding comparator_def 
  proof (intro conjI impI allI)
    fix x y z :: "real_alg"
    let ?r = real_of
    note rc = comparator_compare[where 'a = real, unfolded comparator_def]
    from rc show "invert_order (compare (?r x) (?r y)) = compare (?r y) (?r x)" by blast
    from rc show "compare (?r x) (?r y) = Lt \<Longrightarrow> compare (?r y) (?r z) = Lt \<Longrightarrow> compare (?r x) (?r z) = Lt" by blast
    assume "compare (?r x) (?r y) = Eq"
    with rc have "?r x = ?r y" by blast
    thus "x = y" unfolding real_of_inj .
  qed
qed
end
  
lemma less_eq_real_alg_code[code]: 
  "(less_eq :: real_alg \<Rightarrow> real_alg \<Rightarrow> bool) = le_of_comp compare"
  "(less :: real_alg \<Rightarrow> real_alg \<Rightarrow> bool) = lt_of_comp compare"
  by (rule ord_defs(1)[symmetric], rule ord_defs(2)[symmetric])

instantiation real_alg :: abs
begin

definition abs_real_alg :: "real_alg \<Rightarrow> real_alg" where
  "abs_real_alg x = (if real_of x < 0 then uminus x else x)"
instance ..
end

lemma abs_real_alg: "abs (real_of x) = real_of (abs x)"
  unfolding abs_real_alg_def abs_real_def if_distrib
  by (auto simp: uminus_real_alg)

lemma sgn_real_alg_sound: "sgn x = (if x = 0 then 0 else if 0 < real_of x then 1 else - 1)"
  (is "_ = ?r")
proof -
  have "real_of (sgn x) = sgn (real_of x)" by (simp add: sgn_real_alg)
  also have "\<dots> = real_of ?r" unfolding sgn_real_def if_distrib 
  by (auto simp: less_real_alg_def 
    zero_real_alg_def one_real_alg_def of_rat_real_alg[symmetric] equal_real_alg[symmetric]
    equal_real_def uminus_real_alg[symmetric])
  finally show "sgn x = ?r" unfolding equal_real_alg[symmetric] equal_real_def
    by simp
qed

lemma real_of_of_int: "real_of_rat (rat_of_int z) = real_of (of_int z)"
proof (cases "z \<ge> 0")
  case True
  def n \<equiv> "nat z"
  from True have z: "z = int n" unfolding n_def by simp
  show ?thesis unfolding z
    by (induct n, auto simp: zero_real_alg plus_real_alg[symmetric] one_real_alg)
next
  case False
  def n \<equiv> "nat (-z)"
  from False have z: "z = - int n" unfolding n_def by simp
  show ?thesis unfolding z
    by (induct n, auto simp: zero_real_alg plus_real_alg[symmetric] one_real_alg uminus_real_alg[symmetric]
      minus_real_alg[symmetric] of_rat_diff)
qed

instance real_alg :: linordered_field
  apply standard
     apply (unfold less_eq_real_alg_def plus_real_alg[symmetric], force)
    apply (unfold abs_real_alg_def less_real_alg_def zero_real_alg[symmetric], rule refl)
   apply (unfold less_real_alg_def times_real_alg[symmetric], force)
  apply (rule sgn_real_alg_sound)
  done

instantiation real_alg :: floor_ceiling
begin
lift_definition floor_real_alg :: "real_alg \<Rightarrow> int" is floor_radtc
  by (auto simp: floor_radtc)

lemma floor_real_alg: "floor (real_of x) = floor x"
  by (transfer, auto simp: floor_radtc)

instance 
proof
  fix x :: real_alg
  show "of_int \<lfloor>x\<rfloor> \<le> x \<and> x < of_int (\<lfloor>x\<rfloor> + 1)" unfolding floor_real_alg[symmetric]
    using floor_correct[of "real_of x"] unfolding less_eq_real_alg_def less_real_alg_def 
    real_of_of_int[symmetric] by auto
  hence "x \<le> of_int (\<lfloor>x\<rfloor> + 1)" by auto
  thus "\<exists>z. x \<le> of_int z" by blast
qed
end

lift_definition to_rat_real_alg_main :: "real_alg \<Rightarrow> rat option" is to_rat_radtc
  by (simp add: to_rat_radtc)

lemma to_rat_real_alg_main: "to_rat_real_alg_main x = (if real_of x \<in> \<rat> then 
  Some (THE q. real_of x = of_rat q) else None)"
  by (transfer, simp add: to_rat_radtc)

definition to_rat_real_alg :: "real_alg \<Rightarrow> rat" where
  "to_rat_real_alg x = (case to_rat_real_alg_main x of Some q \<Rightarrow> q | None \<Rightarrow> 0)"

definition is_rat_real_alg :: "real_alg \<Rightarrow> bool" where
  "is_rat_real_alg x = (case to_rat_real_alg_main x of Some q \<Rightarrow> True | None \<Rightarrow> False)"

lemma is_rat_real_alg: "is_rat (real_of x) = (is_rat_real_alg x)"
  unfolding is_rat_real_alg_def is_rat to_rat_real_alg_main by auto

lemma to_rat_real_alg: "to_rat (real_of x) = (to_rat_real_alg x)"
  unfolding to_rat to_rat_real_alg_def to_rat_real_alg_main by auto


subsection \<open>Real Algebraic Numbers as Implementation for Real Numbers\<close>

lemmas real_alg_code_eqns =  
  one_real_alg
  zero_real_alg
  uminus_real_alg
  root_real_alg
  minus_real_alg
  plus_real_alg
  times_real_alg
  inverse_real_alg
  divide_real_alg
  equal_real_alg
  less_real_alg
  less_eq_real_alg
  compare_real_alg
  sgn_real_alg
  abs_real_alg
  floor_real_alg
  is_rat_real_alg
  to_rat_real_alg
  

code_datatype real_of

lemmas real_code_dels = 
  refl[of "op + :: real \<Rightarrow> real \<Rightarrow> real"]
  refl[of "uminus :: real \<Rightarrow> real"]
  refl[of "op - :: real \<Rightarrow> real \<Rightarrow> real"]
  refl[of "op * :: real \<Rightarrow> real \<Rightarrow> real"]
  refl[of "inverse :: real \<Rightarrow> real"]
  refl[of "op / :: real \<Rightarrow> real \<Rightarrow> real"]
  refl[of "floor :: real \<Rightarrow> int"]
  refl[of "HOL.equal :: real \<Rightarrow> real \<Rightarrow> bool"]
  refl[of "compare :: real \<Rightarrow> real \<Rightarrow> order"]
  refl[of "op \<le> :: real \<Rightarrow> real \<Rightarrow> bool"]
  refl[of "op < :: real \<Rightarrow> real \<Rightarrow> bool"]
  refl[of "0 :: real"]
  refl[of "1 :: real"]
  refl[of "sgn :: real \<Rightarrow> real"]
  refl[of "abs :: real \<Rightarrow> real"]
  refl[of root]

lemma real_code_unfold_dels: 
  "of_rat \<equiv> Ratreal" 
  "of_int a \<equiv> (of_rat (of_int a) :: real)" 
  "0 \<equiv> (of_rat 0 :: real)"
  "1 \<equiv> (of_rat 1 :: real)"
  "numeral k \<equiv> (of_rat (numeral k) :: real)"
  "- numeral k \<equiv> (of_rat (- numeral k) :: real)"
  by simp_all


declare real_code_dels[code, code del]
declare real_code_unfold_dels[code_unfold del]
declare real_alg_code_eqns[code]

subsection \<open>Computing Resultants via Integer Polynomials\<close>

text \<open>In order to compute resultants (over rational polynomials with integer coefficients), it 
  is better to directly compute resultants over integer polynomials and then use the 
  specialized @{const resultant_int_poly} algorithm.\<close>

definition poly_add_int :: "int poly \<Rightarrow> int poly \<Rightarrow> int poly" where
  "poly_add_int = poly_add"

definition poly_mult_int :: "int poly \<Rightarrow> int poly \<Rightarrow> int poly" where
  "poly_mult_int = poly_mult"

definition poly_mult'_int :: "int poly \<Rightarrow> int poly \<Rightarrow> int poly" where
  "poly_mult'_int = poly_mult'"
  
lemma poly_add_int_code[code]: 
  "poly_add_int p q = resultant_int_poly (poly_x_minus_y p) (poly_lift q)"
  unfolding poly_add_int_def poly_add_def by simp

lemma poly_mult'_int_code[code]: 
  "poly_mult'_int p q = resultant_int_poly (poly_x_div_y p) (poly_lift q)"
  unfolding poly_mult'_int_def poly_mult'_def by simp

lemma poly_mult_int_code[code]: 
  "poly_mult_int p q = poly_mult'_int (eliminate_zero_divisors p) (eliminate_zero_divisors q)"
  unfolding poly_mult_int_def poly_mult_def poly_mult'_int_def ..

lemma poly_add_via_int_polys_unfold[code_unfold]: "poly_add (normalize_rat_poly p1) (normalize_rat_poly p2)
  = map_poly rat_of_int (poly_add_int (snd (rat_to_int_poly p1)) (snd (rat_to_int_poly p2)))"
proof -
  def q1 \<equiv> "snd (rat_to_int_poly p1)"
  def q2 \<equiv> "snd (rat_to_int_poly p2)"
  show ?thesis unfolding normalize_rat_poly_def q1_def[symmetric] q2_def[symmetric] poly_add_int_def
    by (rule ri.poly_add_hom)
qed

lemma poly_mult_via_int_polys_unfold[code_unfold]: "poly_mult (normalize_rat_poly p1) (normalize_rat_poly p2)
  = map_poly rat_of_int (poly_mult_int (snd (rat_to_int_poly p1)) (snd (rat_to_int_poly p2)))"
proof -
  def q1 \<equiv> "snd (rat_to_int_poly p1)"
  def q2 \<equiv> "snd (rat_to_int_poly p2)"
  show ?thesis unfolding normalize_rat_poly_def q1_def[symmetric] q2_def[symmetric] poly_mult_int_def
    by (rule poly_mult_hom, standard)
qed

end
