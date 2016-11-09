(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>Record Based Version\<close>

text \<open>We provide an implementation for polynomials which may be parametrized
  by the ring- or field-operations. These don't have to be type-based!\<close>

subsubsection \<open>Definitions\<close>

theory Polynomial_Record_Based
imports 
  Arithmetic_Record_Based
  "../Polynomial_Interpolation/Missing_Polynomial"
begin

context
  fixes ops :: "'i arith_ops_record" (structure)
begin
private abbreviation (input) zero where "zero \<equiv> arith_ops_record.zero ops"
private abbreviation (input) one where "one \<equiv> arith_ops_record.one ops"
private abbreviation (input) plus where "plus \<equiv> arith_ops_record.plus ops"
private abbreviation (input) times where "times \<equiv> arith_ops_record.times ops"
private abbreviation (input) minus where "minus \<equiv> arith_ops_record.minus ops"
private abbreviation (input) uminus where "uminus \<equiv> arith_ops_record.uminus ops"
private abbreviation (input) divide where "divide \<equiv> arith_ops_record.divide ops"
private abbreviation (input) inverse where "inverse \<equiv> arith_ops_record.inverse ops"
private abbreviation (input) modulo where "modulo \<equiv> arith_ops_record.modulo ops"
private abbreviation (input) normalize where "normalize \<equiv> arith_ops_record.normalize ops"
private abbreviation (input) unit_factor where "unit_factor \<equiv> arith_ops_record.unit_factor ops"
private abbreviation (input) DP where "DP \<equiv> arith_ops_record.DP ops"

definition is_poly :: "'i list \<Rightarrow> bool" where
  "is_poly xs = (list_all DP xs \<and> (xs = [] \<or> last xs \<noteq> zero))"

definition cCons_i :: "'i \<Rightarrow> 'i list \<Rightarrow> 'i list" 
where
  "cCons_i x xs = (if xs = [] \<and> x = zero then [] else x # xs)"

fun plus_poly_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list" where
  "plus_poly_i (x # xs) (y # ys) = cCons_i (plus x y) (plus_poly_i xs ys)"
| "plus_poly_i xs [] = xs"
| "plus_poly_i [] ys = ys"

definition uminus_poly_i :: "'i list \<Rightarrow> 'i list" where
  [code_unfold]: "uminus_poly_i = map uminus"

fun minus_poly_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list" where
  "minus_poly_i (x # xs) (y # ys) = cCons_i (minus x y) (minus_poly_i xs ys)"
| "minus_poly_i xs [] = xs"
| "minus_poly_i [] ys = uminus_poly_i ys"


abbreviation (input) zero_poly_i :: "'i list" where
  "zero_poly_i \<equiv> []"

definition one_poly_i :: "'i list" where
  [code_unfold]: "one_poly_i = [one]"

definition smult_i :: "'i \<Rightarrow> 'i list \<Rightarrow> 'i list" where
  "smult_i a pp = (if a = zero then [] else map (times a) pp)"

definition times_poly_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list" where
  "times_poly_i pp qq \<equiv> foldr (\<lambda> a pa. plus_poly_i (smult_i a qq) (cCons_i zero pa)) pp zero_poly_i"

definition coeff_i :: "'i list \<Rightarrow> nat \<Rightarrow> 'i" where
  "coeff_i = nth_default zero"

definition degree_i :: "'i list \<Rightarrow> nat" where
  "degree_i pp \<equiv> length pp - 1"

definition lead_coeff_i :: "'i list \<Rightarrow> 'i" where
  "lead_coeff_i pp = (case pp of [] \<Rightarrow> zero | _ \<Rightarrow> last pp)"

definition monic_i :: "'i list \<Rightarrow> bool" where
  "monic_i pp = (lead_coeff_i pp = one)" 

fun minus_poly_rev_list_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list" where
  "minus_poly_rev_list_i (x # xs) (y # ys) = (minus x y) # (minus_poly_rev_list_i xs ys)"
| "minus_poly_rev_list_i xs [] = xs"
| "minus_poly_rev_list_i [] (y # ys) = []"

definition poly_of_list_i :: "'i list \<Rightarrow> 'i list" where
  "poly_of_list_i = strip_while (op = zero)"

fun divmod_poly_one_main_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list 
  \<Rightarrow> nat \<Rightarrow> 'i list \<times> 'i list" where
  "divmod_poly_one_main_i q r d (Suc n) = (let
     a = hd r;
     qqq = cCons_i a q;
     rr = tl (if a = zero then r else minus_poly_rev_list_i r (map (times a) d))
     in divmod_poly_one_main_i qqq rr d n)"
| "divmod_poly_one_main_i q r d 0 = (q,r)"

fun mod_poly_one_main_i :: "'i list \<Rightarrow> 'i list 
  \<Rightarrow> nat \<Rightarrow> 'i list" where
  "mod_poly_one_main_i r d (Suc n) = (let
     a = hd r;
     rr = tl (if a = zero then r else minus_poly_rev_list_i r (map (times a) d))
     in mod_poly_one_main_i rr d n)"
| "mod_poly_one_main_i r d 0 = r"

definition div_field_poly_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list" where 
  "div_field_poly_i cf cg = (
      if cg = [] then zero_poly_i
        else let ilc = inverse (last cg); ch = map (times ilc) cg;
                 q = fst (divmod_poly_one_main_i [] (rev cf) (rev ch) (1 + length cf - length cg))
             in poly_of_list_i ((map (times ilc) q)))"

definition mod_field_poly_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list" where 
  "mod_field_poly_i cf cg = (
      if cg = [] then cf
        else let ilc = inverse (last cg); ch = map (times ilc) cg;
                 r = mod_poly_one_main_i (rev cf) (rev ch) (1 + length cf - length cg)
             in poly_of_list_i (rev r))"

definition normalize_poly_i :: "'i list \<Rightarrow> 'i list" where 
  "normalize_poly_i xs = smult_i (inverse (unit_factor (lead_coeff_i xs))) xs"

definition unit_factor_poly_i :: "'i list \<Rightarrow> 'i list" where 
  "unit_factor_poly_i xs = cCons_i (unit_factor (lead_coeff_i xs)) []"

fun pderiv_main_i :: "'i \<Rightarrow> 'i list \<Rightarrow> 'i list" where
  "pderiv_main_i f (x # xs) = cCons_i (times f x) (pderiv_main_i (plus f one) xs)"
| "pderiv_main_i f [] = []"

definition pderiv_i :: "'i list \<Rightarrow> 'i list" where
  "pderiv_i xs = pderiv_main_i one (tl xs)"

definition dvd_poly_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> bool" where
  "dvd_poly_i xs ys = (\<exists> zs. is_poly zs \<and> ys = times_poly_i xs zs)"

definition irreducible_i :: "'i list \<Rightarrow> bool" where
  "irreducible_i xs = (degree_i xs \<noteq> 0 \<and> (\<forall>q. is_poly q \<longrightarrow> degree_i q \<noteq> 0 \<longrightarrow> degree_i q < degree_i xs 
    \<longrightarrow> \<not> dvd_poly_i q xs))" 

definition poly_ops :: "'i list arith_ops_record" where
  "poly_ops \<equiv> Arith_Ops_Record
      zero_poly_i
      one_poly_i 
      plus_poly_i
      times_poly_i
      minus_poly_i
      uminus_poly_i
      div_field_poly_i
      (\<lambda> _. []) (* not defined *) 
      mod_field_poly_i
      normalize_poly_i
      unit_factor_poly_i
      (\<lambda> i. if i = 0 then [] else [arith_ops_record.of_int ops i])
      is_poly"


definition gcd_poly_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list" where
  "gcd_poly_i = arith_ops.gcd_eucl_i poly_ops"

definition euclid_ext_poly_i :: "'i list \<Rightarrow> 'i list \<Rightarrow> 'i list \<times> 'i list \<times> 'i list" where
  "euclid_ext_poly_i = arith_ops.euclid_ext_i poly_ops"

definition square_free_i :: "'i list \<Rightarrow> bool" where
  "square_free_i xs \<equiv> gcd_poly_i xs (pderiv_i xs) = one_poly_i"
end

(* **************************************************************************** *)
subsubsection \<open>Properties\<close>

lifting_forget poly.lifting

context idom_ops
begin

definition poly_rel :: "'i list \<Rightarrow> 'a poly \<Rightarrow> bool" where
  "poly_rel x x' = (list_all2 R x (coeffs x'))"

lemma right_total_poly_rel[transfer_rule]: 
  "right_total poly_rel"
  using list.right_total_rel[of R] right_total unfolding poly_rel_def right_total_def by auto

lemma bi_unique_poly_rel[transfer_rule]: "bi_unique poly_rel"
  using list.bi_unique_rel[of R] bi_unique unfolding poly_rel_def bi_unique_def coeffs_eq_iff by auto

lemma Domainp_is_poly [transfer_domain_rule]: 
  "Domainp (poly_rel) = (is_poly ops)"
  unfolding poly_rel_def[abs_def] is_poly_def[abs_def]
proof (intro ext iffI, unfold Domainp_iff)
  note DPR = fun_cong[OF list.Domainp_rel[of R, unfolded DPR], unfolded Domainp_iff]
  fix xs
  {
    fix xs'
    assume *: "list_all2 R xs xs'"
    have "(xs' = [] \<or> last (xs') \<noteq> 0) = (xs = [] \<or> last xs \<noteq> zero)"
    proof (cases "xs = []")
      case False
      hence "xs' \<noteq> []" using list_all2_lengthD[OF *] by auto
      from append_butlast_last_id[OF this] obtain y' ys' where xs': "xs' = ys' @ [y']" by metis
      from append_butlast_last_id[OF False] obtain y ys where xs: "xs = ys @ [y]" by metis
      from *[unfolded xs xs'] have "R y y'" by auto
      with zero eq[unfolded rel_fun_def] show ?thesis unfolding xs xs' by simp
    next
      case True
      with * show ?thesis by simp
    qed 
  } note last = this
  let ?DPR = "arith_ops_record.DP ops"
  {
    assume "\<exists>x'. list_all2 R xs (coeffs x')"
    then obtain xs' where *: "list_all2 R xs (coeffs xs')" by auto
    with DPR[of xs] have 1: "list_all ?DPR xs" by auto
    have 2: "coeffs xs' = [] \<or> last (coeffs xs') \<noteq> 0" using last_coeffs_not_0 by auto
    hence "xs = [] \<or> last xs \<noteq> zero" unfolding last[OF *] .
    with 1 show "list_all ?DPR xs \<and> (xs = [] \<or> last xs \<noteq> zero)" by auto
  }
  {
    assume "list_all ?DPR xs \<and> (xs = [] \<or> last xs \<noteq> zero)"
    with DPR[of xs] obtain xs' where *: "list_all2 R xs xs'" and "xs = [] \<or> last xs \<noteq> zero" 
      by auto
    from last[OF *] this(2) have "xs' = [] \<or> last xs' \<noteq> 0" by simp
    hence "coeffs (poly_of_list xs') = xs'" unfolding poly_of_list_impl by auto
    with * show "\<exists>x'. list_all2 R xs (coeffs x')" by metis
  }
qed

(* zero *)
lemma poly_rel_zero[transfer_rule]: "poly_rel zero_poly_i 0"
  unfolding poly_rel_def by auto

(* one *)
lemma poly_rel_one[transfer_rule]: "poly_rel (one_poly_i ops) 1"
  unfolding poly_rel_def one_poly_i_def by (simp add: one)

(* cCons *)
lemma poly_rel_cCons[transfer_rule]: "(R ===> list_all2 R ===> list_all2 R) (cCons_i ops) cCons"
  unfolding cCons_i_def[abs_def] cCons_def[abs_def] 
  by transfer_prover

(* pCons *)
lemma poly_rel_pCons[transfer_rule]: "(R ===> poly_rel ===> poly_rel) (cCons_i ops) pCons"
  unfolding rel_fun_def poly_rel_def coeffs_pCons_eq_cCons cCons_def[symmetric]
  using poly_rel_cCons[unfolded rel_fun_def] by auto

(* equality *)
lemma poly_rel_eq[transfer_rule]: "(poly_rel ===> poly_rel ===> op =) (op =) (op =)"
  unfolding poly_rel_def[abs_def] coeffs_eq_iff[abs_def] rel_fun_def
  by (metis bi_unique bi_uniqueDl bi_uniqueDr list.bi_unique_rel)

(* addition *)
lemma poly_rel_plus[transfer_rule]: "(poly_rel ===> poly_rel ===> poly_rel) (plus_poly_i ops) (op +)"
proof (intro rel_funI)
  fix x1 y1 x2 y2
  assume "poly_rel x1 x2" and "poly_rel y1 y2"
  thus "poly_rel (plus_poly_i ops x1 y1) (x2 + y2)"
    unfolding poly_rel_def coeffs_eq_iff coeffs_plus_eq_plus_coeffs
  proof (induct x1 y1 arbitrary: x2 y2 rule: plus_poly_i.induct)
    case (1 x1 xs1 y1 ys1 X2 Y2)
    from 1(2) obtain x2 xs2 where X2: "coeffs X2 = x2 # coeffs xs2" 
      by (cases X2, auto simp: cCons_def split: if_splits)
    from 1(3) obtain y2 ys2 where Y2: "coeffs Y2 = y2 # coeffs ys2" 
      by (cases Y2, auto simp: cCons_def split: if_splits)
    from 1(2) 1(3) have [transfer_rule]: "R x1 x2" "R y1 y2" 
      and *: "list_all2 R xs1 (coeffs xs2)" "list_all2 R ys1 (coeffs ys2)" unfolding X2 Y2 by auto
    note [transfer_rule] = 1(1)[OF *] 
    show ?case unfolding X2 Y2 by simp transfer_prover
  next
    case (2 xs1 xs2 ys2)
    thus ?case by (cases "coeffs xs2", auto)
  next
    case (3 xs2 y1 ys1 Y2)
    thus ?case by (cases Y2, auto simp: cCons_def)
  qed
qed

(* unary minus *)
lemma poly_rel_uminus[transfer_rule]: "(poly_rel ===> poly_rel) (uminus_poly_i ops) Groups.uminus"
proof (intro rel_funI)
  fix x y
  assume "poly_rel x y" 
  hence [transfer_rule]: "list_all2 R x (coeffs y)" unfolding poly_rel_def .
  show "poly_rel (uminus_poly_i ops x) (-y)"
    unfolding poly_rel_def coeffs_uminus uminus_poly_i_def by transfer_prover
qed

(* subtraction *)
lemma poly_rel_minus[transfer_rule]: "(poly_rel ===> poly_rel ===> poly_rel) (minus_poly_i ops) (op -)"
proof (intro rel_funI)
  fix x1 y1 x2 y2
  assume "poly_rel x1 x2" and "poly_rel y1 y2"
  thus "poly_rel (minus_poly_i ops x1 y1) (x2 - y2)"
    unfolding diff_conv_add_uminus
    unfolding poly_rel_def coeffs_eq_iff coeffs_plus_eq_plus_coeffs coeffs_uminus
  proof (induct x1 y1 arbitrary: x2 y2 rule: minus_poly_i.induct)
    case (1 x1 xs1 y1 ys1 X2 Y2)
    from 1(2) obtain x2 xs2 where X2: "coeffs X2 = x2 # coeffs xs2" 
      by (cases X2, auto simp: cCons_def split: if_splits)
    from 1(3) obtain y2 ys2 where Y2: "coeffs Y2 = y2 # coeffs ys2" 
      by (cases Y2, auto simp: cCons_def split: if_splits)
    from 1(2) 1(3) have [transfer_rule]: "R x1 x2" "R y1 y2" 
      and *: "list_all2 R xs1 (coeffs xs2)" "list_all2 R ys1 (coeffs ys2)" unfolding X2 Y2 by auto
    note [transfer_rule] = 1(1)[OF *] 
    show ?case unfolding X2 Y2 by simp transfer_prover
  next
    case (2 xs1 xs2 ys2)
    thus ?case by (cases "coeffs xs2", auto)
  next
    case (3 xs2 y1 ys1 Y2)
    from 3(1) have id0: "coeffs ys1 = coeffs 0" by (cases ys1, auto)
    have id1: "minus_poly_i ops [] (xs2 # y1) = uminus_poly_i ops (xs2 # y1)" by simp
    from 3(2) have [transfer_rule]: "poly_rel (xs2 # y1) Y2" unfolding poly_rel_def by simp
    show ?case unfolding id0 id1 coeffs_uminus[symmetric] coeffs_plus_eq_plus_coeffs[symmetric]
      poly_rel_def[symmetric] by simp transfer_prover
  qed
qed

(* smult *)
lemma poly_rel_smult[transfer_rule]: "(R ===> poly_rel ===> poly_rel) (smult_i ops) smult"
  unfolding rel_fun_def poly_rel_def coeffs_smult smult_i_def
proof (intro allI impI, goal_cases)
  case (1 x y xs ys)
  note [transfer_rule] = 1
  show ?case by transfer_prover
qed

(* coeffs *)
lemma poly_rel_coeffs[transfer_rule]: "(poly_rel ===> list_all2 R) (\<lambda> x. x) coeffs"
  unfolding rel_fun_def poly_rel_def by auto

(* multiplication *)
lemma poly_rel_times[transfer_rule]: "(poly_rel ===> poly_rel ===> poly_rel) (times_poly_i ops) (op *)"  
proof (intro rel_funI)
  fix x1 y1 x2 y2
  assume "poly_rel x1 x2" and [transfer_rule]: "poly_rel y1 y2"
  hence [transfer_rule]: "list_all2 R x1 (coeffs x2)" 
    unfolding poly_rel_def by auto
  show "poly_rel (times_poly_i ops x1 y1) (x2 * y2)"
    unfolding poly_rel_def coeffs_eq_iff times_poly_def times_poly_i_def fold_coeffs_def
    by transfer_prover
qed

(* coeff *)  
lemma poly_rel_coeff[transfer_rule]: "(poly_rel ===> op = ===> R) (coeff_i ops) coeff"
  unfolding poly_rel_def rel_fun_def coeff_i_def nth_default_coeffs_eq[symmetric]
proof (intro allI impI, clarify)
  fix x y n
  assume [transfer_rule]: "list_all2 R x (coeffs y)"
  show "R (nth_default zero x n) (nth_default 0 (coeffs y) n)" by transfer_prover
qed

(* degree *)
lemma poly_rel_degree[transfer_rule]: "(poly_rel ===> op =) degree_i degree"
  unfolding poly_rel_def rel_fun_def degree_i_def degree_eq_length_coeffs 
  by (simp add: list_all2_lengthD)

(* lead_coeff *)
lemma lead_coeff_i_def': "lead_coeff_i ops x = (coeff_i ops) x (degree_i x)"
  unfolding lead_coeff_i_def degree_i_def coeff_i_def
proof (cases x, auto, goal_cases)
  case (1 a xs)
  hence id: "last xs = last (a # xs)" by auto
  show ?case unfolding id by (subst last_conv_nth_default, auto)
qed

lemma poly_rel_lead_coeff[transfer_rule]: "(poly_rel ===> R) (lead_coeff_i ops) lead_coeff"
  unfolding lead_coeff_i_def'[abs_def] lead_coeff_def[abs_def] by transfer_prover

(* poly_of_list *)  
lemma poly_rel_poly_of_list[transfer_rule]: "(list_all2 R ===> poly_rel) (poly_of_list_i ops) poly_of_list"
  unfolding rel_fun_def poly_of_list_i_def poly_rel_def poly_of_list_impl
proof (intro allI impI, goal_cases)
  case (1 x y)
  note [transfer_rule] = this
  show ?case by transfer_prover
qed

(* minus_poly_rev_list *)
lemma poly_rel_minus_poly_rev_list[transfer_rule]: 
  "(list_all2 R ===> list_all2 R ===> list_all2 R) (minus_poly_rev_list_i ops) minus_poly_rev_list"
proof (intro rel_funI, goal_cases)
  case (1 x1 x2 y1 y2)
  thus ?case
  proof (induct x1 y1 arbitrary: x2 y2 rule: minus_poly_rev_list_i.induct)
    case (1 x1 xs1 y1 ys1 X2 Y2)
    from 1(2) obtain x2 xs2 where X2: "X2 = x2 # xs2" by (cases X2, auto)
    from 1(3) obtain y2 ys2 where Y2: "Y2 = y2 # ys2" by (cases Y2, auto)
    from 1(2) 1(3) have [transfer_rule]: "R x1 x2" "R y1 y2" 
      and *: "list_all2 R xs1 xs2" "list_all2 R ys1 ys2" unfolding X2 Y2 by auto
    note [transfer_rule] = 1(1)[OF *] 
    show ?case unfolding X2 Y2 by (simp, intro conjI, transfer_prover+)
  next
    case (2 xs1 xs2 ys2)
    thus ?case by (cases xs2, auto)
  next
    case (3 xs2 y1 ys1 Y2)
    thus ?case by (cases Y2, auto)
  qed
qed

(* division *)
lemma divmod_poly_one_main_i: assumes len: "n \<le> length Y" and rel: "list_all2 R x X" "list_all2 R y Y"
    "list_all2 R z Z" and n: "n = N"
 shows "rel_prod (list_all2 R) (list_all2 R) (divmod_poly_one_main_i ops x y z n)
    (divmod_poly_one_main_list X Y Z N)"
   using len rel unfolding n 
proof (induct N arbitrary: x X y Y z Z)
  case (Suc n x X y Y z Z)
  from Suc(2,4) have [transfer_rule]: "R (hd y) (hd Y)" by (cases y; cases Y, auto)  
  note [transfer_rule] = Suc(3-5)
  have id: "?case = (rel_prod (list_all2 R) (list_all2 R)
     (divmod_poly_one_main_i ops (cCons_i ops (hd y) x)
       (tl (if hd y = zero then y else minus_poly_rev_list_i ops y (map (times (hd y)) z))) z n)
     (divmod_poly_one_main_list (cCons (hd Y) X)
       (tl (if hd Y = 0 then Y else minus_poly_rev_list Y (map (op * (hd Y)) Z))) Z n))"
     by (simp add: Let_def)
  show ?case unfolding id
  proof (rule Suc(1), goal_cases)
    case 1
    show ?case using Suc(2) by simp 
  qed (transfer_prover+)
qed simp

(* modulo *)
lemma mod_poly_one_main_i: assumes len: "n \<le> length X" and rel: "list_all2 R x X" "list_all2 R y Y"
    and n: "n = N"
 shows "list_all2 R (mod_poly_one_main_i ops x y n)
    (mod_poly_one_main_list X Y N)"
   using len rel unfolding n 
proof (induct N arbitrary: x X y Y)
  case (Suc n y Y z Z)
  from Suc(2,3) have [transfer_rule]: "R (hd y) (hd Y)" by (cases y; cases Y, auto)  
  note [transfer_rule] = Suc(3-4)
  have id: "?case = (list_all2 R
     (mod_poly_one_main_i ops
       (tl (if hd y = zero then y else minus_poly_rev_list_i ops y (map (times (hd y)) z))) z n)
     (mod_poly_one_main_list 
       (tl (if hd Y = 0 then Y else minus_poly_rev_list Y (map (op * (hd Y)) Z))) Z n))"
     by (simp add: Let_def)
  show ?case unfolding id
  proof (rule Suc(1), goal_cases)
    case 1
    show ?case using Suc(2) by simp 
  qed (transfer_prover+)
qed simp

(* pderiv *)
lemma poly_rel_pderiv [transfer_rule]: "(poly_rel ===> poly_rel) (pderiv_i ops) pderiv"
proof (intro rel_funI, unfold poly_rel_def coeffs_pderiv_code pderiv_i_def pderiv_coeffs_def)
  fix xs xs'
  assume "list_all2 R xs (coeffs xs')"
  then obtain ys ys' y y' where id: "tl xs = ys" "tl (coeffs xs') = ys'" "one = y" "1 = y'" and 
    R: "list_all2 R ys ys'" "R y y'"
    by (cases xs; cases "coeffs xs'"; auto simp: one)
  show "list_all2 R (pderiv_main_i ops one (tl xs))
            (pderiv_coeffs_code 1 (tl (coeffs xs')))"
    unfolding id using R
  proof (induct ys ys' arbitrary: y y' rule: list_all2_induct)
    case (Cons x xs x' xs' y y')
    note [transfer_rule] = Cons(1,2,4)
    have "R (plus y one) (y' + 1)"  by transfer_prover
    note [transfer_rule] = Cons(3)[OF this]
    show ?case by (simp, transfer_prover)
  qed simp
qed 

lemma poly_rel_dvd[transfer_rule]: "(poly_rel ===> poly_rel ===> op =) (dvd_poly_i ops) (op dvd)"
  unfolding dvd_poly_i_def[abs_def] dvd_def[abs_def] 
  by (transfer_prover_start, transfer_step+, auto)

lemma poly_rel_irreducible[transfer_rule]: "(poly_rel ===> op =) (irreducible_i ops) irreducible"
  unfolding irreducible_i_def[abs_def] irreducible_def[abs_def] 
  by (transfer_prover_start, transfer_step+, auto)

lemma poly_rel_monic[transfer_rule]: "(poly_rel ===> op =) (monic_i ops) monic"
  unfolding monic_i_def[abs_def] lead_coeff_def[symmetric] by transfer_prover

lemma idom_ops_poly: "idom_ops (poly_ops ops) poly_rel"
  by (unfold_locales, auto simp: poly_ops_def  
  bi_unique_poly_rel 
  right_total_poly_rel
  poly_rel_times
  poly_rel_zero 
  poly_rel_one
  poly_rel_minus
  poly_rel_uminus
  poly_rel_plus
  poly_rel_eq
  Domainp_is_poly)
end

context field_ops
begin
(* division *)
lemma poly_rel_div[transfer_rule]: "(poly_rel ===> poly_rel ===> poly_rel) 
  (div_field_poly_i ops) (op div)"
proof (intro rel_funI, goal_cases)
  case (1 x X y Y)
  note [transfer_rule] = this
  note listall = this[unfolded poly_rel_def]
  note defs = div_field_poly_impl div_field_poly_impl_def div_field_poly_i_def Let_def
  show ?case 
  proof (cases "y = []")
    case True
    with 1(2) have nil: "coeffs Y = []" unfolding poly_rel_def by auto
    show ?thesis unfolding defs True nil poly_rel_def by auto
  next
    case False
    from append_butlast_last_id[OF False] obtain ys yl where y: "y = ys @ [yl]" by metis
    from False listall have "coeffs Y \<noteq> []" by auto
    from append_butlast_last_id[OF this] obtain Ys Yl where Y: "coeffs Y = Ys @ [Yl]" by metis
    from listall have [transfer_rule]: "R yl Yl" by (simp add: y Y)
    have id: "last (coeffs Y) = Yl" "last (y) = yl" 
      "\<And> t e. (if y = [] then t else e) = e"
      "\<And> t e. (if coeffs Y = [] then t else e) = e" unfolding y Y by auto
    have [transfer_rule]: "(rel_prod (list_all2 R) (list_all2 R)) 
      (divmod_poly_one_main_i ops [] (rev x) (rev (map (times (inverse yl)) y))
        (1 + length x - length y))
      (divmod_poly_one_main_list [] (rev (coeffs X))
                (rev (map (op * (Fields.inverse Yl)) (coeffs Y)))
                (1 + length (coeffs X) - length (coeffs Y)))"
    proof (rule divmod_poly_one_main_i, goal_cases)
      case 5
      from listall show ?case by (simp add: list_all2_lengthD)
    next
      case 1
      from listall show ?case by (simp add: list_all2_lengthD Y)
    qed transfer_prover+      
    show ?thesis unfolding defs id by transfer_prover
  qed
qed

(* modulo *)
lemma poly_rel_mod[transfer_rule]: "(poly_rel ===> poly_rel ===> poly_rel) 
  (mod_field_poly_i ops) (op mod)"
proof (intro rel_funI, goal_cases)
  case (1 x X y Y)
  note [transfer_rule] = this
  note listall = this[unfolded poly_rel_def]
  note defs = mod_poly_code mod_field_poly_i_def Let_def
  show ?case 
  proof (cases "y = []")
    case True
    with 1(2) have nil: "coeffs Y = []" unfolding poly_rel_def by auto
    show ?thesis unfolding defs True nil poly_rel_def by (simp add: listall)
  next
    case False
    from append_butlast_last_id[OF False] obtain ys yl where y: "y = ys @ [yl]" by metis
    from False listall have "coeffs Y \<noteq> []" by auto
    from append_butlast_last_id[OF this] obtain Ys Yl where Y: "coeffs Y = Ys @ [Yl]" by metis
    from listall have [transfer_rule]: "R yl Yl" by (simp add: y Y)
    have id: "last (coeffs Y) = Yl" "last (y) = yl" 
      "\<And> t e. (if y = [] then t else e) = e"
      "\<And> t e. (if coeffs Y = [] then t else e) = e" unfolding y Y by auto
    have [transfer_rule]: "list_all2 R
      (mod_poly_one_main_i ops (rev x) (rev (map (times (inverse yl)) y))
        (1 + length x - length y))
      (mod_poly_one_main_list (rev (coeffs X))
                (rev (map (op * (Fields.inverse Yl)) (coeffs Y)))
                (1 + length (coeffs X) - length (coeffs Y)))"
    proof (rule mod_poly_one_main_i, goal_cases)
      case 4
      from listall show ?case by (simp add: list_all2_lengthD)
    next
      case 1
      from listall show ?case by (simp add: list_all2_lengthD Y)
    qed transfer_prover+      
    show ?thesis unfolding defs id by transfer_prover
  qed
qed

(* normalize *)
lemma poly_rel_normalize [transfer_rule]: "(poly_rel ===> poly_rel) 
  (normalize_poly_i ops) Rings.normalize"
  unfolding normalize_poly_old_def[abs_def] normalize_poly_i_def[abs_def]
  by transfer_prover

(* unit_factor *)
lemma poly_rel_unit_factor [transfer_rule]: "(poly_rel ===> poly_rel) 
  (unit_factor_poly_i ops) Rings.unit_factor"
  unfolding unit_factor_poly_def[abs_def] unit_factor_poly_i_def[abs_def]
  unfolding monom_0 by transfer_prover

lemma idom_divide_ops_poly: "idom_divide_ops (poly_ops ops) poly_rel"
proof -
  interpret poly: idom_ops "poly_ops ops" poly_rel by (rule idom_ops_poly)
  show ?thesis
    by (unfold_locales, simp add: poly_rel_div poly_ops_def)
qed

lemma euclidean_ring_ops_poly: "euclidean_ring_ops (poly_ops ops) poly_rel"
proof -
  interpret poly: idom_ops "poly_ops ops" poly_rel by (rule idom_ops_poly)
  have id: "arith_ops_record.normalize (poly_ops ops) = normalize_poly_i ops"
    "arith_ops_record.unit_factor (poly_ops ops) = unit_factor_poly_i ops"
    unfolding poly_ops_def by simp_all
  show ?thesis
    by (unfold_locales, simp add: poly_rel_mod poly_ops_def, unfold id, 
      simp add: poly_rel_normalize, insert poly_rel_div poly_rel_unit_factor, 
      auto simp: poly_ops_def)
qed

(* gcd poly *)
lemma poly_rel_gcd [transfer_rule]: "(poly_rel ===> poly_rel ===> poly_rel) (gcd_poly_i ops) gcd"
proof -
  interpret poly: euclidean_ring_ops "poly_ops ops" poly_rel by (rule euclidean_ring_ops_poly)
  show ?thesis using poly.gcd_eucl_i unfolding gcd_poly_i_def gcd_poly_def gcd_eucl_eq_gcd_factorial .
qed

(* euclid_ext poly *)
lemma poly_rel_euclid_ext [transfer_rule]: "(poly_rel ===> poly_rel ===> 
  rel_prod poly_rel (rel_prod poly_rel poly_rel)) (euclid_ext_poly_i ops) euclid_ext"
proof -
  interpret poly: euclidean_ring_ops "poly_ops ops" poly_rel by (rule euclidean_ring_ops_poly)
  show ?thesis using poly.euclid_ext_i unfolding euclid_ext_poly_i_def .
qed 

end

(* ********************************************************** *)

context idom_ops
begin
lemma assumes "poly_rel xs x" "poly_rel ys y" 
  shows "times_poly_i ops xs ys = times_poly_i ops ys xs"
proof -
  note [transfer_rule] = assms
  have "x * y = y * x" by simp
  from this[untransferred] show ?thesis .
qed
end
end
