(*  Title:       Executable multivariate polynomials
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
    License:     LGPL
*)

(*
Copyright 2010 Christian Sternagel, René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

section {* Polynomials *}

theory Polynomials
imports 
  "../Abstract-Rewriting/SN_Orders"
  "../Matrix/Utility" 
begin

subsection {*
Polynomials represented as trees
*}
datatype ('v,'a)tpoly = PVar 'v | PNum 'a | PSum "('v,'a)tpoly list" | PMult "('v,'a)tpoly list"

type_synonym ('v,'a)assign = "'v \<Rightarrow> 'a"

fun eval_tpoly :: "('v,'a :: semiring_1)assign \<Rightarrow> ('v,'a)tpoly \<Rightarrow> 'a"
where "eval_tpoly \<alpha> (PVar x) = \<alpha> x"
   |  "eval_tpoly \<alpha> (PNum a) = a"
   |  "eval_tpoly \<alpha> (PSum []) = 0"
   |  "eval_tpoly \<alpha> (PSum (p # ps)) = eval_tpoly \<alpha> p + eval_tpoly \<alpha> (PSum ps)"
   |  "eval_tpoly \<alpha> (PMult []) = 1"
   |  "eval_tpoly \<alpha> (PMult (p # ps)) = eval_tpoly \<alpha> p * eval_tpoly \<alpha> (PMult ps)"

subsection {* Polynomials represented in normal form as lists of monomials *}
text {*
  The internal representation of polynomials is a sum of products of monomials with coefficients
  where all coefficients are non-zero, and all monomials are different
*}
 
text {* Definition of type @{text monom} *}


type_synonym 'v monom = "('v \<times> nat)list" 
text {* 
\begin{itemize}
\item $[(x,n),(y,m)]$ represent $x^n \cdot y^m$
\item invariants: all powers are $\geq 1$ and each variable occurs at most once \\
   hence: $[(x,1),(y,2),(x,2)]$ will not occur, but $[(x,3),(y,2)]$;
          $[(x,1),(y,0)]$ will not occur, but $[(x,1)]$
\end{itemize}
*}

definition monom_inv :: "'v monom \<Rightarrow> bool"
where "monom_inv m \<equiv> (\<forall> (x,n) \<in> set m. 1 \<le> n) \<and> distinct (map fst m)"


fun eval_monom :: "('v,'a :: comm_semiring_1)assign \<Rightarrow> ('v monom) \<Rightarrow> 'a"
where "eval_monom \<alpha> [] = 1"
   |  "eval_monom \<alpha> ((x,p) # m) = eval_monom \<alpha> m * (\<alpha> x)^p"

lemma eval_monom_list[simp]: "eval_monom \<alpha> (m @ n) = eval_monom \<alpha> m * eval_monom \<alpha> n"
  by (induct m, auto simp: field_simps)


text {*
equality of monomials should be able to identify $x^2 \cdot y$ with $y \cdot x^2$,
essentially, it checks for permutations. Checking of permutations 
suffices, since in $x^2 \cdot x^1 = x^3$, the left-hand side should not
be constructed due to the invariant, that every variable occurs at
most once in a monomial.
*}
fun eq_monom :: "'v monom \<Rightarrow> 'v monom \<Rightarrow> bool" (infix "=m" 51) where
  "[] =m n = (n = [])" 
| "(x,p) # m =m n =
  (case List.extract (\<lambda>yq. fst yq = x) n of
    None \<Rightarrow> False
  | Some (n1,(_,q),n2) \<Rightarrow> p = q \<and> m =m (n1 @ n2))"

lemma eq_monom_refl: "m =m m"
proof (induct m)
  case (Cons xp m)
  show ?case 
  proof (cases xp)
    case (Pair x p)
    show ?thesis
      by (simp add: Pair Cons extract_Cons_code)
  qed
qed simp

definition sum_var_list :: "'v monom \<Rightarrow> 'v \<Rightarrow> nat"
where "sum_var_list m x \<equiv> listsum (map (\<lambda> (y,c). if x = y then c else 0) m)"

lemma sum_var_list_not: "x \<notin> fst ` set m \<Longrightarrow> sum_var_list m x = 0"
unfolding sum_var_list_def
  by (induct m, auto)

text {*
show that equality of monomials is equivalent to statement that 
all variables occur with the same (accumulated) power;
afterwards properties like transitivity, etc. are easy to prove *}
lemma eq_monom_sum_var_list: assumes "monom_inv m" and "monom_inv n"
  shows "eq_monom m n = (\<forall> x. sum_var_list m x = sum_var_list n x)" (is "?l = ?r")
using assms
proof (induct m arbitrary: n)
  case Nil
  show ?case 
  proof (cases n)
    case (Cons yp nn)
    obtain y p where yp: "yp = (y,p)" by (cases yp, auto)
    with Cons Nil(2)[unfolded monom_inv_def] have p: "0 < p" by auto
    show ?thesis by (simp add: Cons, rule exI[of _ y], simp add: sum_var_list_def yp p)
  qed simp
next
  case (Cons xp m)
  obtain x p where xp: "xp = (x,p)" by (cases xp, auto)
  with Cons(2) have p: "0 < p" and x: "x \<notin> fst ` set m" and m: "monom_inv m" unfolding monom_inv_def by auto
  show ?case 
  proof (cases "List.extract (\<lambda> yq. fst yq = x) n")
    case None
    hence not1: "x \<notin> fst ` set n" by (auto simp: extract_None_iff)
    show ?thesis
      by (simp add: xp Cons None, rule exI[of _ x], simp add: sum_var_list_not[OF not1], simp add: sum_var_list_def p)
  next
    case (Some res)
    obtain n1 yq n2 where "res = (n1,yq,n2)" by (cases res, auto)
    then obtain y q where "res = (n1,(y,q),n2)" by (cases yq, auto)
    with extract_SomeE[OF Some[simplified this]] have n: "n = n1 @ (x,q) # n2" and res: "res = (n1,(x,q),n2)"  by auto
    from Cons(3)[unfolded n] have q: "1 \<le> q" and n1n2: "x \<notin> fst ` (set (n1 @ n2))" and n1n2m: "monom_inv (n1 @ n2)" unfolding  monom_inv_def by auto
    show ?thesis 
    proof (cases "p = q")
      case False
      have "sum_var_list ((x,p) # m) x = p + sum_var_list m x" unfolding sum_var_list_def by auto
      also have "\<dots> = p" using sum_var_list_not[OF x] by simp
      also have "\<dots> \<noteq> q" using False .
      also have "q = q + sum_var_list (n1 @ n2) x" using sum_var_list_not[OF n1n2] by simp
      also have "\<dots> = sum_var_list n x" unfolding n sum_var_list_def by auto
      finally have not2: "sum_var_list ((x,p) # m) x \<noteq> sum_var_list n x" . 
      show ?thesis
        by (simp add: xp Some res False, rule exI[of _ x], rule not2)
    next
      case True 
      {
        fix y
        have "(sum_var_list m y = sum_var_list (n1 @ n2) y) =
          (sum_var_list ((x,q) # m) y = sum_var_list (n1 @ (x,q) # n2) y)"
          by (unfold sum_var_list_def, cases "x = y", auto)
      }
      hence id: "(\<forall> y. sum_var_list m y = sum_var_list (n1 @ n2) y) = 
          (\<forall> y. sum_var_list ((x,q) # m) y = sum_var_list (n1 @ (x,q) # n2) y)"
        by blast
      show ?thesis 
        by (simp add: xp Some res True Cons(1)[OF m n1n2m], simp only: n, rule id)
    qed
  qed
qed
      

lemma eq_monom_sym: assumes m: "monom_inv m" and n: "monom_inv n" shows "(m =m n) = (n =m m)"
  by (simp add: eq_monom_sum_var_list[OF m n] eq_monom_sum_var_list[OF n m] sum_var_list_def, auto)

lemma eq_monom_trans: assumes m1: "monom_inv m1" and m2: "monom_inv m2" and m3: "monom_inv m3" shows 
  "m1 =m m2 \<Longrightarrow> m2 =m m3 \<Longrightarrow> m1 =m m3"
  by (simp add: eq_monom_sum_var_list[OF m1 m2] eq_monom_sum_var_list[OF m2 m3] eq_monom_sum_var_list[OF m1 m3] sum_var_list_def)

text {*
show that equality of monomials implies equal evaluations *}    
lemma eq_monom: "m =m n \<Longrightarrow> eval_monom \<alpha> m = eval_monom \<alpha> n"
proof (induct m arbitrary: n)
  case (Cons xp m) note mCons = this
  show ?case
  proof (cases xp)
    case (Pair x p)
    show ?thesis 
    proof (cases "List.extract (\<lambda> yq. fst yq = x) n")
      case None
      with Cons Pair show ?thesis by auto
    next
      case (Some res)
      obtain n1 yq n2 where "res = (n1,yq,n2)" by (cases res, auto)
      then obtain y q where res: "res = (n1,(y,q),n2)" by (cases yq, auto)
      from extract_SomeE[OF Some[simplified res]] mCons(2)  Some Pair res have n: "n = n1 @ (x,p) # n2" and rec: "m =m (n1 @ n2)" by auto
      show ?thesis by (simp add: Pair mCons(1)[OF rec] n field_simps)
    qed
  qed
qed simp

text {*
  equality of monomials is also a complete for several carriers, e.g. the naturals, integers, where $x^p = x^q$ implies $p = q$.
  note that it is not complete for carriers like the Booleans where e.g. $x^{Suc(m)} = x^{Suc(n)}$ for all $n,m$.
*}
lemma eq_monom_inv: 
  fixes m :: "'v monom"
  assumes exp_inject: "\<And> p q :: nat. \<exists> base :: 'a :: poly_carrier. base^p = base^q \<Longrightarrow> p = q" and m: "monom_inv m" and n: "monom_inv n" shows "(m =m n) = (\<forall> \<alpha> :: ('v,'a :: poly_carrier)assign. eval_monom \<alpha> m = eval_monom \<alpha> n)"
proof(intro iffI allI, rule eq_monom)
  assume "\<forall> \<alpha> :: ('v,'a :: poly_carrier)assign. eval_monom \<alpha> m = eval_monom \<alpha> n"
  with m n show "m =m n"
  proof (induct m arbitrary: n)
    case Nil
    show ?case 
    proof (cases n)
      case (Cons yq nn)
      with Nil obtain y q where yq: "yq = (y,q)" and "1 \<le> q" by (cases yq, auto simp: monom_inv_def)
      then obtain qq where q: "q = Suc (qq)" by (cases q, auto)
      from Nil(3) have "1 = eval_monom (\<lambda> x. 0 :: 'a) n" (is "?one = _") by simp
      also have "\<dots> = 0" by (simp add: Cons yq q)
      finally show ?thesis by simp
    qed simp
  next
    case (Cons xp m) note mCons = this
    show ?case
    proof (cases xp)
      case (Pair x p)
      let ?ass = "(\<lambda> v y. if x = y then v else 1 :: 'a)"
      {
        fix v :: 'a and m :: "'v monom"
        assume "x \<notin> fst ` (set m)"
        hence "eval_monom (?ass v) m = 1"
        proof (induct m)
          case (Cons yp m)
          thus ?case 
            by (cases yp, cases "fst yp = x", auto)
        qed simp
      } note ass = this
      from Cons(2)[unfolded Pair] obtain pp where p: "p = Suc pp" and xm: "x \<notin> fst ` (set m)" unfolding monom_inv_def by (cases p, auto)
      from ass[OF xm] have "\<And> v. eval_monom (?ass v) (xp # m) = v * v^pp" by (simp add: Pair p)
      with Cons(4) have eval: "\<And> v. eval_monom (?ass v) n = v * v^pp" by auto
      show ?thesis 
      proof (cases "List.extract (\<lambda> yq. fst yq = x) n")
        case None
        with ass[of n] have "\<And> v. eval_monom (?ass v) n = 1" by (auto simp: extract_None_iff)
        from this[of 0] eval[of 0] show ?thesis by simp
      next
        case (Some res)
        obtain n1 yq n2 where "res = (n1,yq,n2)" by (cases res, auto)
        then obtain y q where "res = (n1,(y,q),n2)" by (cases yq, auto)        
        from extract_SomeE[OF Some[simplified this]] mCons(2)  Some Pair this have n: "n = n1 @ (x,q) # n2" and res: "res = (n1,(x,q),n2)" by auto
        from mCons(3)[unfolded n] have xn: "x \<notin> fst ` (set (n1 @ n2))" unfolding monom_inv_def by auto
        have "\<And> v. eval_monom (?ass v) n = v^q * eval_monom (?ass v) (n1 @ n2)" unfolding n by (auto simp: field_simps)
        from eval[unfolded this ass[OF xn]] have id: "\<And> v :: 'a. v^p = v^q" using p by auto
        from exp_inject[of p q] id have pq: "p = q" by auto
        have rec: "((xp # m) =m n) = (m =m (n1 @ n2))" by (simp add: Pair Some res pq)
        have ass: "\<forall>\<alpha> :: ('v,'a)assign. eval_monom \<alpha> m = eval_monom \<alpha> (n1 @ n2)"
        proof
          fix \<alpha> :: "('v,'a)assign"
          show "eval_monom \<alpha> m = eval_monom \<alpha> (n1 @ n2)"
          proof (rule ccontr)
            assume neq: "\<not> ?thesis"
            let ?ass =  "\<lambda> y :: 'v. if x = y then 1 :: 'a else \<alpha> y"
            {
              fix m :: "'v monom"
              assume "x \<notin> fst ` set m"
              hence "eval_monom \<alpha> m = eval_monom ?ass m"
                by (induct m, auto)
            } note ass = this
            have "eval_monom \<alpha> (n1 @ n2) = eval_monom ?ass (n1 @ n2)" using ass[OF xn] .
            also have "\<dots> = eval_monom ?ass n" unfolding n by auto
            also have "\<dots> = eval_monom ?ass ((xp # m))" using mCons(4) by auto
            also have "\<dots> = eval_monom ?ass m" unfolding Pair by simp
            also have "\<dots> = eval_monom \<alpha> m" using ass[OF xm] by simp 
            also have "\<dots> \<noteq> eval_monom \<alpha> (n1 @ n2)" by (rule neq)
            finally show False by simp
          qed
        qed
        from mCons(2) mCons(3) have "monom_inv m" and "monom_inv (n1 @ n2)" unfolding monom_inv_def n by auto
        from mCons(1)[OF this ass] rec show ?thesis by simp
      qed
    qed    
  qed
qed simp  

declare eq_monom.simps[simp del]

abbreviation monom_vars :: "'v monom \<Rightarrow> 'v set"
  where "monom_vars m \<equiv> fst ` set m"

fun monom_mult :: "'v monom \<Rightarrow> 'v monom \<Rightarrow> 'v monom"
where "monom_mult [] n = n"
  |   "monom_mult ((x,p) # m) n = (case List.extract (\<lambda> yq. fst yq = x) n of
                           None \<Rightarrow> (x,p) # monom_mult m n 
                         | Some (n1,(_,q),n2) \<Rightarrow> (x,p+q) # monom_mult m (n1 @ n2))"

lemma monom_mult_vars: "monom_vars (monom_mult m1 m2) = monom_vars m1 \<union> monom_vars m2"
proof (induct m1 arbitrary: m2)
  case (Cons xp m) note mCons = this
  show ?case
  proof (cases xp)
    case (Pair x p)
    show ?thesis 
    proof (cases "List.extract (\<lambda> yq. fst yq = x) m2")
      case None
      with Cons Pair show ?thesis by auto 
    next
      case (Some res)
      obtain n1 yq n2 where "res = (n1,yq,n2)" by (cases res, auto)
      then obtain y q where res: "res = (n1,(y,q),n2)" by (cases yq, auto)
      from extract_SomeE[OF Some[simplified res]] Some Pair res have m2: "m2 = n1 @ (x,q) # n2"
        and rec: "monom_mult (xp # m) m2 = (x, p+q) # monom_mult m (n1 @ n2)" by auto
      show ?thesis by (simp only: rec, simp add: mCons Pair m2)
    qed
  qed
qed simp


lemma monom_mult_inv: "monom_inv m1 \<Longrightarrow> monom_inv m2 \<Longrightarrow> monom_inv (monom_mult m1 m2)"
proof (induct m1 arbitrary: m2)
  case Nil thus ?case by (simp add: monom_inv_def)
next
  case (Cons xp m1)
  obtain x p where xp: "xp = (x,p)" by (cases xp) auto
  from xp Cons(2) have m1: "monom_inv m1" and x: "x \<notin> monom_vars m1" and p: "1 \<le> p" by (auto simp: monom_inv_def)
  show ?case 
  proof (cases "List.extract (\<lambda> yq. fst yq = x) m2")
    case None
    hence "x \<notin> monom_vars m2" by (auto simp: extract_None_iff)
    from x this have x: "x \<notin> monom_vars (monom_mult m1 m2)" by (simp add: monom_mult_vars)
    with None Cons(1)[OF m1 Cons(3)] x p xp show ?thesis by (auto simp: monom_inv_def)
  next
    case (Some res)
    obtain n1 yq n2 where "res = (n1,yq,n2)" by (cases res, auto)
    then obtain y q where res: "res = (n1,(y,q),n2)" by (cases yq, auto)
    from extract_SomeE[OF Some[simplified res]] Some xp res have m2: "m2 = n1 @ (x,q) # n2"
      and rec: "monom_mult (xp # m1) m2 = (x, p+q) # monom_mult m1 (n1 @ n2)" by auto
    from Cons(3) m2 have xn1: "x \<notin> monom_vars (n1 @ n2)"
      and n1n2: "monom_inv (n1 @ n2)" and q: "1 \<le> q" by (auto simp: monom_inv_def)
    from x xn1 have x: "x \<notin> monom_vars (monom_mult m1 (n1 @ n2))" by (simp add: monom_mult_vars)
    from p q have pq: "1 \<le> p + q" by auto
    from Cons(1)[OF m1 n1n2] pq xn1
    show ?thesis 
      by (simp only: rec, auto simp: monom_inv_def x)
  qed
qed

lemma monom_mult_inj: assumes m: "monom_inv m" and m1: "monom_inv m1" and m2: "monom_inv m2"
  and eq: "monom_mult m m1 =m monom_mult m m2"
  shows "m1 =m m2"
proof -
  {
    fix x n 
    have "sum_var_list (monom_mult m n) x = sum_var_list m x + sum_var_list n x"
    proof (induct m arbitrary: n, simp add: sum_var_list_def)
      case (Cons yp m)
      obtain y p where yp: "yp = (y,p)" by (cases yp, auto)
      hence id: "sum_var_list (yp # m) x = (if x = y then p else 0) + sum_var_list m x" unfolding sum_var_list_def by auto
      show ?case
      proof (cases "List.extract (\<lambda> zq. fst zq = y) n")
        case None
        have "sum_var_list (monom_mult (yp # m) n) x = (if x = y then p else 0) + sum_var_list (monom_mult m n) x"
          by (simp add: yp None sum_var_list_def)
        thus ?thesis
          by (simp add: Cons id)
      next
        case (Some res)
        obtain n1 zq n2 where "res = (n1,zq,n2)" by (cases res, auto)
        then obtain z q where res: "res = (n1,(z,q),n2)" by (cases zq, auto)
        from extract_SomeE[OF Some[simplified res]] Some res yp have n: "n = n1 @ (y,q) # n2"
          and rec: "sum_var_list (monom_mult (yp # m) n) x  = (if x = y then p+q else 0) + sum_var_list (monom_mult m (n1 @ n2)) x" 
          unfolding sum_var_list_def by auto
        show ?thesis
          by (simp only: rec Cons id, simp add: n sum_var_list_def)
      qed
    qed
  } note main = this
  from eq main show ?thesis
    by  (auto simp: eq_monom_sum_var_list[OF m1 m2] eq_monom_sum_var_list[OF monom_mult_inv[OF m m1] monom_mult_inv[OF m m2]])
qed


lemma monom_mult[simp]: "eval_monom \<alpha> (monom_mult m n) = eval_monom \<alpha> m * eval_monom \<alpha> n"
proof (induct m arbitrary: n)
  case (Cons xp m) note mCons = this
  show ?case
  proof (cases xp)
    case (Pair x p)
    show ?thesis 
    proof (cases "List.extract (\<lambda> yq. fst yq = x) n")
      case None
      with Cons Pair show ?thesis by (auto simp: field_simps)
    next
      case (Some res)
      obtain n1 yq n2 where "res = (n1,yq,n2)" by (cases res, auto)
      then obtain y q where res: "res = (n1,(y,q),n2)" by (cases yq, auto)
      from extract_SomeE[OF Some[simplified res]] Some Pair res have n: "n = n1 @ (x,q) # n2" 
        and rec: "monom_mult (xp # m) n = (x, p+q) # monom_mult m (n1 @ n2)" by auto
      show ?thesis by (simp only: rec, simp add: Pair mCons[of "n1 @ n2"] n field_simps power_add)
    qed
  qed
qed simp

declare monom_mult.simps[simp del]

text {*
Polynomials are represented with as sum of monomials multiplied by some coefficient 
*}
type_synonym ('v,'a)poly = "('v monom \<times> 'a)list"

text {*
The polynomials we construct satisfy the following invariants:
\begin{itemize}
\item 
   all monomials satisfy their invariant
\item all coefficients are non-zero
\item no two equivalent monomials occur in the list 
\end{itemize}
*}

fun distinct_eq :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "distinct_eq _ [] = True"
| "distinct_eq eq (x # xs) = ((\<forall> y \<in> set xs. \<not> (eq y x)) \<and> distinct_eq eq xs)"

lemma distinct_eq_append: "distinct_eq eq (xs @ ys) = (distinct_eq eq xs \<and> distinct_eq eq ys \<and> (\<forall> x \<in> set xs. \<forall> y \<in> set ys. \<not> (eq y x)))"
  by (induct xs, auto)

definition poly_inv :: "('v,'a :: zero)poly \<Rightarrow> bool"
  where "poly_inv p \<equiv> (\<forall> (m,c) \<in> set p. monom_inv m \<and> c \<noteq> 0) \<and> distinct_eq (\<lambda> (m1,_) (m2,_). m1 =m m2) p"


abbreviation eval_monomc where "eval_monomc \<alpha> mc \<equiv> eval_monom \<alpha> (fst mc) * (snd mc)"

fun eval_poly :: "('v,'a :: comm_semiring_1)assign \<Rightarrow> ('v,'a)poly \<Rightarrow> 'a"
where "eval_poly \<alpha> [] = 0"
   |  "eval_poly \<alpha> (mc # p) = eval_monomc \<alpha> mc + eval_poly \<alpha> p"


fun poly_add :: "('v,'a)poly \<Rightarrow> ('v,'a :: semiring_0)poly \<Rightarrow> ('v,'a)poly"
where "poly_add [] q = q"
   |  "poly_add ((m,c) # p) q = (case List.extract (\<lambda> mc. fst mc =m m) q of
                                None \<Rightarrow> (m,c) # poly_add p q
                              | Some (q1,(_,d),q2) \<Rightarrow> if (c+d = 0) then poly_add p (q1 @ q2) else (m,c+d) # poly_add p (q1 @ q2))"

lemma eval_poly_append[simp]: "eval_poly \<alpha> (mc1 @ mc2) = eval_poly \<alpha> mc1 + eval_poly \<alpha> mc2"
  by (induct mc1, auto simp: field_simps)


abbreviation poly_monoms :: "('v,'a)poly \<Rightarrow> 'v monom set"
  where "poly_monoms p \<equiv> fst ` set p"

lemma poly_add_monoms: "poly_monoms (poly_add p1 p2) \<subseteq> poly_monoms p1 \<union> poly_monoms p2"
proof (induct p1 arbitrary: p2)
  case (Cons mc p)
  obtain m c where mc: "mc = (m,c)" by (cases mc, auto)
  hence m: "m \<in> poly_monoms (mc # p1)" by auto
  show ?case
  proof (cases "List.extract (\<lambda> nd. fst nd =m m) p2")
    case None
    with Cons m show ?thesis by (auto simp: mc)
  next
    case (Some res)
    obtain q1 md q2 where res: "res = (q1,md,q2)" by (cases res, auto)
    from extract_SomeE[OF Some[simplified res]] res obtain m' d where q: "p2 = q1 @ (m',d) # q2" and res: "res = (q1,(m',d),q2)" and mm': "m' =m m" by (cases md, auto)
    show ?thesis
      by (simp add: mc Some res, rule subset_trans[OF Cons[of "q1 @ q2"]], auto simp: q)
  qed
qed simp
  

lemma poly_add_inv: "poly_inv p \<Longrightarrow> poly_inv q \<Longrightarrow> poly_inv (poly_add p q)"
proof (induct p arbitrary: q)
  case (Cons mc p)
  obtain m c where mc: "mc = (m,c)" by (cases mc, auto)
  with Cons(2) have p: "poly_inv p" and m: "monom_inv m" and c: "c \<noteq> 0" and mp: "\<forall> (mm,dd) \<in> set p. (\<not> mm =m m)" unfolding poly_inv_def by auto
  show ?case
  proof (cases "List.extract (\<lambda> mc. fst mc =m m) q")
    case None
    hence mq: "\<forall> (mm,dd) \<in> set q. \<not> mm =m m" by (auto simp: extract_None_iff)
    { 
      fix mm dd
      assume "(mm,dd) \<in> set (poly_add p q)"
      with poly_add_monoms have "mm \<in> poly_monoms p \<or> mm \<in> poly_monoms q" by force
      hence "\<not> mm =m m"
      proof
        assume "mm \<in> poly_monoms p"
        thus ?thesis using mp  by auto
      next
        assume "mm \<in> poly_monoms q"
        thus ?thesis using mq by auto
      qed
    } note main = this
    show ?thesis using Cons(1)[OF p Cons(3)] unfolding poly_inv_def by (auto simp add: None mc m c main)
  next
    case (Some res)
    obtain q1 md q2 where res: "res = (q1,md,q2)" by (cases res, auto)
    from extract_SomeE[OF Some[simplified res]] res obtain m' d where q: "q = q1 @ (m',d) # q2" and res: "res = (q1,(m',d),q2)" and mm': "m' =m m" by (cases md, auto)
    from q Cons(3) have q1q2: "poly_inv (q1 @ q2)" and m': "monom_inv m'" unfolding poly_inv_def by (auto simp: distinct_eq_append)
    from Cons(1)[OF p q1q2]  have main1: "poly_inv (poly_add p (q1 @ q2))" .
    {
      fix mm dd
      assume "(mm,dd) \<in> set (poly_add p (q1 @ q2))"
      with poly_add_monoms have "mm \<in> poly_monoms p \<or> mm \<in> poly_monoms (q1 @ q2)" by force
      hence "\<not> mm =m m"
      proof
        assume "mm \<in> poly_monoms p"
        thus ?thesis using mp  by auto
      next
        assume member: "mm \<in> poly_monoms (q1 @ q2)"
        with q1q2 have mm: "monom_inv mm" unfolding poly_inv_def by auto
        from member have "mm \<in> poly_monoms q1 \<or> mm \<in> poly_monoms q2" by auto
        hence mmm': "\<not> mm =m m'"
        proof
          assume "mm \<in> poly_monoms q2"
          with Cons(3)[simplified q]
          show ?thesis unfolding poly_inv_def by (auto simp: distinct_eq_append)
        next
          assume "mm \<in> poly_monoms q1"
          with Cons(3)[simplified q]
          have "\<not> m' =m mm" unfolding poly_inv_def by (auto simp: distinct_eq_append)
          thus ?thesis using eq_monom_sym[OF m' mm] by blast
        qed
        show ?thesis
        proof
          assume "mm =m m"
          from this mm'[simplified eq_monom_sym[OF m' m]]
          have "mm =m m'" using eq_monom_trans[OF mm m m'] by blast
          with mmm' show False by simp
        qed
      qed
    } note main2 = this
    show ?thesis 
      by (simp add: mc Some res main1, simp add: poly_inv_def m, auto simp: main1[unfolded poly_inv_def] main2)
  qed
qed simp
    


lemma poly_add[simp]: "eval_poly \<alpha> (poly_add p q) = eval_poly \<alpha> p + eval_poly \<alpha> q"
proof (induct p arbitrary: q)
  case (Cons mc p)
  obtain m c where mc: "mc = (m,c)" by (cases mc, auto)
  show ?case
  proof (cases "List.extract (\<lambda> mc. fst mc =m m) q")
    case None
    show ?thesis by (simp add: Cons[of q] mc None field_simps)
  next
    case (Some res)
    obtain q1 md q2 where res: "res = (q1,md,q2)" by (cases res, auto)
    from extract_SomeE[OF Some[simplified res]] res obtain m' d where q: "q = q1 @ (m',d) # q2" and m': "m' =m m" and res: "res = (q1,(m',d),q2)" by (cases md, auto)
    {
      fix x
      assume c: "c + d = 0"
      have "c * x + d * x = (c + d) * x" by (auto simp: field_simps)
      also have "\<dots> = 0 * x" by (simp only: c)
      finally have "c * x + d * x = 0" by simp
    } note id = this
    show ?thesis 
      by (simp add: Cons[of "q1 @ q2"] mc Some res, simp only: q, simp add: eq_monom[OF m'] field_simps, auto simp: field_simps id)
  qed
qed simp

declare poly_add.simps[simp del]

fun monom_mult_poly :: "('v monom \<times> 'a) \<Rightarrow> ('v,'a :: semiring_0)poly \<Rightarrow> ('v,'a)poly"
where "monom_mult_poly _ [] = []"
    | "monom_mult_poly (m,c) ((m',d) # p) = (if c * d = 0 then monom_mult_poly (m,c) p else (monom_mult m m', c * d) # monom_mult_poly (m,c) p)"

lemma monom_mult_poly_inv: assumes m: "monom_inv m" shows "poly_inv p \<Longrightarrow> poly_inv (monom_mult_poly (m,c) p)"
proof (induct p)
  case Nil thus ?case by (simp add: poly_inv_def)
next
  case (Cons md p)
  obtain m' d where md: "md = (m',d)" by (cases md, auto)
  with Cons(2) have m': "monom_inv m'" and p: "poly_inv p" unfolding poly_inv_def by auto
  from Cons(1)[OF p] have prod: "poly_inv (monom_mult_poly (m,c) p)" .
  {
    fix mm dd
    assume one: "(mm,dd) \<in> set (monom_mult_poly (m,c) p)"
      and two: "mm =m monom_mult m m'"
    have "poly_monoms (monom_mult_poly (m,c) p) \<subseteq> monom_mult m ` poly_monoms p" 
    proof (induct p, simp)
      case (Cons md p)
      thus ?case
        by (cases md, auto)
    qed
    with one have "mm \<in> monom_mult m ` poly_monoms p" by force
    then obtain mmm where mmm: "mmm \<in> poly_monoms p" and mm: "mm = monom_mult m mmm" by blast
    from Cons(2)[simplified md] mmm have not1: "\<not> mmm =m m'" and mmm: "monom_inv mmm" unfolding poly_inv_def by (auto simp: distinct_eq_append)
    from mm two have "monom_mult m mmm =m monom_mult m m'" by simp
    from monom_mult_inj[OF m mmm m' this] not1 
    have False by simp
  } 
  thus ?case 
    by (simp add: md prod, intro impI, simp add: poly_inv_def, simp add: monom_mult_inv[OF m m'], auto simp: prod[simplified poly_inv_def])
qed

lemma monom_mult_poly[simp]: "eval_poly \<alpha> (monom_mult_poly mc p) = eval_monomc \<alpha> mc * eval_poly \<alpha> p"
proof (cases mc)
  case (Pair m c)
  show ?thesis
  proof (simp add: Pair, induct p)
    case (Cons nd q)
    obtain n d where nd: "nd = (n,d)" by (cases nd, auto)
    show ?case
    proof (cases "c * d = 0")
      case False
      thus ?thesis by (simp add: nd Cons field_simps)
    next
      case True
      let ?l = "c * (d * (eval_monom \<alpha> m * eval_monom \<alpha> n))"
      have "?l = (c * d) * (eval_monom \<alpha> m * eval_monom \<alpha> n)" 
        by (simp only: field_simps)
      also have "\<dots> = 0" by (simp only: True, simp add: field_simps)
      finally have l: "?l = 0" .
      show ?thesis 
        by (simp add: nd Cons True, simp add: field_simps l) 
    qed
  qed simp
qed

declare monom_mult_poly.simps[simp del]

fun poly_mult :: "('v,'a :: semiring_0)poly \<Rightarrow> ('v,'a)poly \<Rightarrow> ('v,'a)poly" 
where "poly_mult [] q = []"
   |  "poly_mult (mc # p) q = poly_add (monom_mult_poly mc q) (poly_mult p q)"

lemma poly_mult_inv: assumes p: "poly_inv p" and q: "poly_inv q"
  shows "poly_inv (poly_mult p q)"
using p
proof (induct p)
  case Nil thus ?case by (simp add: poly_inv_def)
next
  case (Cons mc p)
  obtain m c where mc: "mc = (m,c)" by (cases mc, auto)
  with Cons(2) have m: "monom_inv m" and p: "poly_inv p" unfolding poly_inv_def by auto
  show ?case
    by (simp add: mc, rule poly_add_inv[OF monom_mult_poly_inv[OF m q] Cons(1)[OF p]])
qed

lemma poly_mult[simp]: "eval_poly \<alpha> (poly_mult p q) = eval_poly \<alpha> p * eval_poly \<alpha> q"
proof (induct p)
  case (Cons mc p)
  thus ?case
    by (simp add: field_simps)
qed simp

declare poly_mult.simps[simp del]

definition zero_poly :: "('v,'a)poly"
where "zero_poly \<equiv> []"

lemma zero_poly_inv: "poly_inv zero_poly" unfolding zero_poly_def poly_inv_def by auto

definition one_poly :: "('v,'a :: semiring_1)poly"
where "one_poly \<equiv> [([],1)]"

lemma one_poly_inv: "poly_inv one_poly" unfolding one_poly_def poly_inv_def monom_inv_def by auto

lemma poly_zero_add: "poly_add zero_poly p = p" unfolding zero_poly_def using poly_add.simps by auto

lemma poly_zero_mult: "poly_mult zero_poly p = zero_poly" unfolding zero_poly_def using poly_mult.simps by auto

text {* equality of polynomials *}
definition eq_poly :: "('v,'a :: comm_semiring_1)poly \<Rightarrow> ('v,'a)poly \<Rightarrow> bool" (infix "=p" 51)
where "p =p q \<equiv> \<forall> \<alpha>. eval_poly \<alpha> p = eval_poly \<alpha> q"

lemma poly_one_mult: "poly_mult one_poly p =p p" 
unfolding eq_poly_def one_poly_def
by (simp)

lemma eq_poly_refl[simp]: "p =p p" unfolding eq_poly_def by auto

lemma eq_poly_trans[trans]: "\<lbrakk>p1 =p p2; p2 =p p3\<rbrakk> \<Longrightarrow> p1 =p p3"
using assms unfolding eq_poly_def by auto

lemma poly_add_comm: "poly_add p q =p poly_add q p" unfolding eq_poly_def by (auto simp: field_simps)

lemma poly_add_assoc: "poly_add p1 (poly_add p2 p3) =p poly_add (poly_add p1 p2) p3" unfolding eq_poly_def by (auto simp: field_simps)

lemma poly_mult_comm: "poly_mult p q =p poly_mult q p" unfolding eq_poly_def by (auto simp: field_simps)

lemma poly_mult_assoc: "poly_mult p1 (poly_mult p2 p3) =p poly_mult (poly_mult p1 p2) p3" unfolding eq_poly_def by (auto simp: field_simps)

lemma poly_distrib: "poly_mult p (poly_add q1 q2) =p poly_add (poly_mult p q1) (poly_mult p q2)" unfolding eq_poly_def by (auto simp: field_simps)


subsection {* Computing normal forms of polynomials *}
fun
  poly_of :: "('v,'a :: comm_semiring_1)tpoly \<Rightarrow> ('v,'a)poly"
where "poly_of (PNum i) = (if i = 0 then [] else [([],i)])"
    | "poly_of (PVar x) = [([(x,1)],1)]"
    | "poly_of (PSum []) = zero_poly" 
    | "poly_of (PSum (p # ps)) = (poly_add (poly_of p) (poly_of (PSum ps)))"
    | "poly_of (PMult []) = one_poly" 
    | "poly_of (PMult (p # ps)) = (poly_mult (poly_of p) (poly_of (PMult ps)))"

text {*
  evaluation is preserved by poly\_of
*}
lemma poly_of: "eval_poly \<alpha> (poly_of p) = eval_tpoly \<alpha> p"
by (induct p rule: poly_of.induct, (simp add: zero_poly_def one_poly_def)+)

text {*
  poly\_of only generates polynomials that satisfy the invariant
*}
lemma poly_of_inv: "poly_inv (poly_of p)"
by (induct p rule: poly_of.induct, 
    simp add: poly_inv_def monom_inv_def,
    simp add: poly_inv_def monom_inv_def,
    simp add: zero_poly_inv,
    simp add: poly_add_inv,
    simp add: one_poly_inv,
    simp add: poly_mult_inv)


subsection {* Powers and substitutions of polynomials *}
fun poly_power :: "('v,'a :: comm_semiring_1)poly \<Rightarrow> nat \<Rightarrow> ('v,'a)poly"
where "poly_power _ 0 = one_poly"
  | "poly_power p (Suc n) = poly_mult p (poly_power p n)"

lemma poly_power[simp]: "eval_poly \<alpha> (poly_power p n) = (eval_poly \<alpha> p) ^ n"
  by (induct n, auto simp: one_poly_def)

lemma poly_power_inv: assumes p: "poly_inv p" 
  shows "poly_inv (poly_power p n)"
  by (induct n, simp add: one_poly_inv, simp add: poly_mult_inv[OF p])


declare poly_power.simps[simp del]

fun monom_subst :: "('v \<Rightarrow> ('w,'a :: comm_semiring_1)poly) \<Rightarrow> 'v monom \<Rightarrow> ('w,'a)poly"
where "monom_subst \<sigma> [] = one_poly"
  | "monom_subst \<sigma> ((x,p) # m) = poly_mult (poly_power (\<sigma> x) p) (monom_subst \<sigma> m)"

lemma monom_subst_inv: assumes sub: "\<And> x. poly_inv (\<sigma> x)" 
  shows "poly_inv (monom_subst \<sigma> m)"
proof (induct m)
  case Nil thus ?case by (simp add: one_poly_inv)
next
  case (Cons xp m)
  obtain x p where xp: "xp = (x,p)" by (cases xp, auto)
  show ?case by (simp add: xp, rule poly_mult_inv[OF poly_power_inv[OF sub] Cons])
qed

lemma monom_subst[simp]: "eval_poly \<alpha> (monom_subst \<sigma> m) = eval_monom (\<lambda> v. eval_poly \<alpha> (\<sigma> v)) m"
  by (induct m, simp add: one_poly_def, auto simp: field_simps)

declare monom_subst.simps[simp del]

fun poly_subst :: "('v \<Rightarrow> ('w,'a :: comm_semiring_1)poly) \<Rightarrow> ('v,'a)poly \<Rightarrow> ('w,'a)poly"
where "poly_subst \<sigma> [] = zero_poly"
  | "poly_subst \<sigma> ((m,c) # p) = poly_add (poly_mult [([],c)] (monom_subst \<sigma> m)) (poly_subst \<sigma> p)"

lemma poly_subst_inv: assumes sub: "\<And> x. poly_inv (\<sigma> x)" and p: "poly_inv p"
  shows "poly_inv (poly_subst \<sigma> p)"
using p
proof (induct p)
  case Nil thus ?case by (simp add: zero_poly_inv)
next
  case (Cons mc p)
  obtain m c where mc: "mc = (m,c)" by (cases mc, auto)
  with Cons(2) have c: "c \<noteq> 0" and p: "poly_inv p" unfolding poly_inv_def by auto
  from c have c: "poly_inv [([],c)]" unfolding poly_inv_def monom_inv_def by auto
  show ?case 
    by (simp add: mc, rule poly_add_inv[OF poly_mult_inv[OF c monom_subst_inv[OF sub]] Cons(1)[OF p]])
qed

lemma poly_subst: "eval_poly \<alpha> (poly_subst \<sigma> p) = eval_poly (\<lambda> v. eval_poly \<alpha> (\<sigma> v)) p"
  by (induct p, simp add: zero_poly_def, auto simp: field_simps)

lemma eval_poly_subst: 
      assumes eq: "\<And> w. f w = eval_poly g (q w)"
      shows "eval_poly f p = eval_poly g (poly_subst q p)" 
proof (induct p)
  case Nil thus ?case by (simp add: zero_poly_def)
next
  case (Cons mc p)
  obtain m c where mc: "mc = (m,c)" by (cases mc, auto)
  have id: "eval_monom f m =  eval_monom (\<lambda>v. eval_poly g (q v)) m"
  proof (induct m)
    case (Cons wp m)
    obtain w p where wp: "wp = (w,p)" by (cases wp, auto)
    show ?case
      by (simp add: wp Cons eq)
  qed simp
  show ?case
    by (simp add: mc Cons id, simp add: field_simps)
qed

(* the list of variables occuring in p *)
definition poly_vars_list :: "('v,'a)poly \<Rightarrow> 'v list"
where "poly_vars_list p = remdups (concat (map (map fst o fst) p))"

definition poly_vars :: "('v,'a)poly \<Rightarrow> 'v set"
where "poly_vars p = set (concat (map (map fst o fst) p))"

lemma poly_vars_list[simp]: "set (poly_vars_list p) = poly_vars p" 
  unfolding poly_vars_list_def poly_vars_def by auto

lemma poly_vars: assumes eq: "\<And> w. w \<in> poly_vars p \<Longrightarrow> f w = g w"
  shows "poly_subst f p = poly_subst g p" 
using eq
proof (induct p)
  case (Cons mc p)
  hence rec: "poly_subst f p = poly_subst g p" unfolding poly_vars_def by auto
  show ?case
  proof (cases mc)
    case (Pair m c)
    with Cons(2) have "\<And> w. w \<in> set (map fst m) \<Longrightarrow> f w = g w" unfolding poly_vars_def by auto
    hence "monom_subst f m = monom_subst g m"
    proof (induct m)
      case Nil thus ?case by (simp add: monom_subst.simps)
    next
      case (Cons wn m)
      hence rec: "monom_subst f m = monom_subst g m" and eq: "f (fst wn) = g (fst wn)" by auto
      show ?case
      proof (cases wn)
        case (Pair w n)
        with eq rec show ?thesis by (auto simp: monom_subst.simps)
      qed
    qed
    with rec Pair show ?thesis by auto
  qed
qed simp

lemma poly_var: assumes pv: "v \<notin> poly_vars p" and diff: "\<And> w. v \<noteq> w \<Longrightarrow> f w = g w"
  shows "poly_subst f p = poly_subst g p"
proof (rule poly_vars)
  fix w
  assume "w \<in> poly_vars p"
  thus "f w = g w" using pv diff by (cases "v = w", auto)
qed

lemma eval_poly_vars: assumes "\<And> x. x \<in> poly_vars p \<Longrightarrow> \<alpha> x = \<beta> x"
  shows "eval_poly \<alpha> p = eval_poly \<beta> p"
using assms
proof (induct p)
  case Nil thus ?case by simp
next
  case (Cons m p)
  from Cons(2) have "\<And> x. x \<in> poly_vars p \<Longrightarrow> \<alpha> x = \<beta> x" unfolding poly_vars_def by auto
  from Cons(1)[OF this] have IH: "eval_poly \<alpha> p = eval_poly \<beta> p" .
  obtain xs c where m: "m = (xs,c)" by force
  from Cons(2) have "\<And> x. x \<in> set (map fst xs) \<Longrightarrow> \<alpha> x = \<beta> x" unfolding poly_vars_def m by auto
  hence "eval_monom \<alpha> xs = eval_monom \<beta> xs"
  proof (induct xs)
    case Nil thus ?case by simp
  next
    case (Cons xi xs)
    hence IH: "eval_monom \<alpha> xs = eval_monom \<beta> xs" by auto
    obtain x i where xi: "xi = (x,i)" by force
    from Cons(2) xi have "\<alpha> x = \<beta> x" by auto
    with IH show ?case unfolding xi by auto
  qed
  thus ?case unfolding eval_poly.simps IH m by auto
qed

           
declare poly_subst.simps[simp del]



subsection {*
  Polynomial orders
*}

definition pos_assign :: "('v,'a :: ordered_semiring_0)assign \<Rightarrow> bool"
where "pos_assign \<alpha> = (\<forall> x. \<alpha> x \<ge> 0)"

definition poly_ge :: "('v,'a :: poly_carrier)poly \<Rightarrow> ('v,'a)poly \<Rightarrow> bool" (infix "\<ge>p" 51)
where "p \<ge>p q = (\<forall> \<alpha>. pos_assign \<alpha> \<longrightarrow> eval_poly \<alpha> p \<ge> eval_poly \<alpha> q)"

lemma poly_ge_refl[simp]: "p \<ge>p p"
unfolding poly_ge_def using ge_refl by auto

lemma poly_ge_trans[trans]: "\<lbrakk>p1 \<ge>p p2; p2 \<ge>p p3\<rbrakk> \<Longrightarrow> p1 \<ge>p p3"
using assms unfolding poly_ge_def using ge_trans by blast


lemma pos_assign_monom: fixes \<alpha> :: "('v,'a :: poly_carrier)assign"
  assumes pos: "pos_assign \<alpha>"
  shows "eval_monom \<alpha> m \<ge> 0"
proof (induct m)
  case Nil thus ?case by (simp add: one_ge_zero)
next
  case (Cons xp m)
  show ?case
  proof (cases xp)
    case (Pair x p)
    from pos[unfolded pos_assign_def] have ge: "\<alpha> x \<ge> 0" by simp
    have ge: "\<alpha> x ^ p \<ge> 0"
    proof (induct p)
      case 0 thus ?case by (simp add: one_ge_zero)
    next
      case (Suc p)
      from ge_trans[OF times_left_mono[OF ge Suc] times_right_mono[OF ge_refl ge]]
      show ?case by (simp add: field_simps)
    qed
    from ge_trans[OF times_right_mono[OF Cons ge] times_left_mono[OF ge_refl Cons]]
    show ?thesis
      by (simp add: Pair)
  qed
qed

lemma pos_assign_poly:   assumes pos: "pos_assign \<alpha>"
  and p: "p \<ge>p zero_poly"
  shows "eval_poly \<alpha> p \<ge> 0"
proof -
  from p[unfolded poly_ge_def zero_poly_def] pos 
  show ?thesis by auto
qed


lemma poly_add_ge_mono: assumes "p1 \<ge>p p2" shows "poly_add p1 q \<ge>p poly_add p2 q"
using assms unfolding poly_ge_def by (auto simp: field_simps plus_left_mono)

lemma poly_mult_ge_mono: assumes "p1 \<ge>p p2" and "q \<ge>p zero_poly"
  shows "poly_mult p1 q \<ge>p poly_mult p2 q"
using assms unfolding poly_ge_def zero_poly_def by (auto simp: times_left_mono)

context poly_order_carrier
begin

definition poly_gt :: "('v,'a)poly \<Rightarrow> ('v,'a)poly \<Rightarrow> bool" (infix ">p" 51)
where "p >p q = (\<forall> \<alpha>. pos_assign \<alpha> \<longrightarrow> eval_poly \<alpha> p \<succ> eval_poly \<alpha> q)"

lemma poly_gt_imp_poly_ge: "p >p q \<Longrightarrow> p \<ge>p q" unfolding poly_ge_def poly_gt_def using gt_imp_ge by blast

abbreviation poly_GT :: "('v,'a)poly rel"
where "poly_GT \<equiv> {(p,q) | p q. p >p q \<and> q \<ge>p zero_poly}"

lemma poly_compat: "\<lbrakk>p1 \<ge>p p2; p2 >p p3\<rbrakk> \<Longrightarrow> p1 >p p3"
using assms unfolding poly_ge_def poly_gt_def using compat by blast

lemma poly_compat2: "\<lbrakk>p1 >p p2; p2 \<ge>p p3\<rbrakk> \<Longrightarrow> p1 >p p3"
using assms unfolding poly_ge_def poly_gt_def using compat2 by blast

lemma poly_gt_trans[trans]: "\<lbrakk>p1 >p p2; p2 >p p3\<rbrakk> \<Longrightarrow> p1 >p p3"
using assms unfolding poly_gt_def using gt_trans by blast

lemma poly_GT_SN: "SN poly_GT"
proof
  fix f :: "nat \<Rightarrow> ('c,'a)poly"
  assume f: "\<forall> i. (f i, f (Suc i)) \<in> poly_GT"
  have pos: "pos_assign ((\<lambda> x. 0) :: ('v,'a)assign)" (is "pos_assign ?ass") unfolding pos_assign_def using ge_refl by auto
  obtain g where g: "\<And> i. g i = eval_poly ?ass (f i)" by auto
  from f pos have "\<forall> i. g (Suc i) \<ge> 0 \<and> g i \<succ> g (Suc i)" unfolding poly_gt_def g using pos_assign_poly by auto
  with SN show False unfolding SN_defs by blast 
qed
end

text {* monotonicity of polynomials *}

lemma eval_monom_mono: assumes fg: "\<And> x. (f :: ('v,'a :: poly_carrier)assign) x \<ge> g x" 
  and g: "\<And> x. g x \<ge> 0"
  shows "eval_monom f m \<ge> eval_monom g m" "eval_monom g m \<ge> 0"
proof - 
  have "eval_monom f m \<ge> eval_monom g m \<and> eval_monom g m \<ge> 0"
  proof (induct m)
    case Nil show ?case using one_ge_zero by (auto simp: ge_refl)
  next
    case (Cons xd m)
    hence IH1: " eval_monom f m \<ge> eval_monom g m" and IH2: "eval_monom g m \<ge> 0" by auto
    obtain x d where xd: "xd = (x,d)" by force
    from pow_mono[OF fg g, of x d] have fgd: "f x ^ d \<ge> g x ^ d" and gd: "g x ^ d \<ge> 0" by auto
    show ?case unfolding xd eval_monom.simps
    proof (rule conjI, rule ge_trans[OF times_left_mono[OF pow_ge_zero IH1] times_right_mono[OF IH2 fgd]])
      show "f x \<ge> 0" by (rule ge_trans[OF fg g])
      show "eval_monom g m * g x ^ d \<ge> 0"
        by (rule mult_ge_zero[OF IH2 gd])
    qed
  qed
  thus "eval_monom f m \<ge> eval_monom g m" "eval_monom g m \<ge> 0" by auto
qed

definition poly_weak_mono_all :: "('v,'a :: poly_carrier)poly \<Rightarrow> bool" where 
  "poly_weak_mono_all p \<equiv> \<forall> (\<alpha> :: ('v,'a)assign) \<beta>. (\<forall> x. \<alpha> x \<ge> \<beta> x) 
    \<longrightarrow> pos_assign \<beta> \<longrightarrow> eval_poly \<alpha> p \<ge> eval_poly \<beta> p"

lemma poly_weak_mono_all_E: assumes p: "poly_weak_mono_all p" and 
  ge: "\<And> x. f x \<ge>p g x \<and> g x \<ge>p zero_poly"
  shows "poly_subst f p \<ge>p poly_subst g p"
  unfolding poly_ge_def poly_subst
proof (intro allI impI, rule p[unfolded poly_weak_mono_all_def, rule_format])
  fix \<alpha> :: "('c,'b)assign" and x
  show "pos_assign \<alpha> \<Longrightarrow> eval_poly \<alpha> (f x) \<ge> eval_poly \<alpha> (g x)" using ge[of x] unfolding poly_ge_def by auto
next
  fix \<alpha> :: "('c,'b)assign"
  assume alpha: "pos_assign \<alpha>"
  show "pos_assign (\<lambda>v. eval_poly \<alpha> (g v))" 
    unfolding pos_assign_def
  proof
    fix x
    show "eval_poly \<alpha> (g x) \<ge> 0"
    using ge[of x] unfolding poly_ge_def zero_poly_def using alpha by auto
  qed
qed

definition poly_weak_mono :: "('v,'a :: poly_carrier)poly \<Rightarrow> 'v \<Rightarrow> bool" where 
  "poly_weak_mono p v \<equiv> \<forall> (\<alpha> :: ('v,'a)assign) \<beta>. (\<forall> x. v \<noteq> x \<longrightarrow> \<alpha> x = \<beta> x) \<longrightarrow> pos_assign \<beta> \<longrightarrow> \<alpha> v \<ge> \<beta> v \<longrightarrow> eval_poly \<alpha> p \<ge> eval_poly \<beta> p"

lemma poly_weak_mono_E: assumes p: "poly_weak_mono p v"
  and fgw: "\<And> w. v \<noteq> w \<Longrightarrow> f w = g w"
  and g: "\<And> w. g w \<ge>p zero_poly" 
  and fgv: "f v \<ge>p g v"
  shows "poly_subst f p \<ge>p poly_subst g p"
  unfolding poly_ge_def poly_subst
proof (intro allI impI, rule p[unfolded poly_weak_mono_def, rule_format])
  fix \<alpha> :: "('c,'b)assign"
  show "pos_assign \<alpha> \<Longrightarrow> eval_poly \<alpha> (f v) \<ge> eval_poly \<alpha> (g v)" using fgv unfolding poly_ge_def by auto
next
  fix \<alpha> :: "('c,'b)assign"
  assume alpha: "pos_assign \<alpha>"
  show "pos_assign (\<lambda>v. eval_poly \<alpha> (g v))" 
    unfolding pos_assign_def
  proof
    fix x
    show "eval_poly \<alpha> (g x) \<ge> 0"
    using g[of x] unfolding poly_ge_def zero_poly_def using alpha by auto
  qed
next
  fix \<alpha> :: "('c,'b)assign" and x
  assume v: "v \<noteq> x"
  show "pos_assign \<alpha> \<Longrightarrow> eval_poly \<alpha> (f x) = eval_poly \<alpha> (g x)" using fgw[OF v] unfolding poly_ge_def by auto
qed

definition poly_weak_anti_mono :: "('v,'a :: poly_carrier)poly \<Rightarrow> 'v \<Rightarrow> bool" where 
  "poly_weak_anti_mono p v \<equiv> \<forall> (\<alpha> :: ('v,'a)assign) \<beta>. (\<forall> x. v \<noteq> x \<longrightarrow> \<alpha> x = \<beta> x) \<longrightarrow> pos_assign \<beta> \<longrightarrow> \<alpha> v \<ge> \<beta> v \<longrightarrow> eval_poly \<beta> p \<ge> eval_poly \<alpha> p"

lemma poly_weak_anti_mono_E: assumes p: "poly_weak_anti_mono p v"
  and fgw: "\<And> w. v \<noteq> w \<Longrightarrow> f w = g w"
  and g: "\<And> w. g w \<ge>p zero_poly" 
  and fgv: "f v \<ge>p g v"
  shows "poly_subst g p \<ge>p poly_subst f p"
  unfolding poly_ge_def poly_subst
proof (intro allI impI, rule p[unfolded poly_weak_anti_mono_def, rule_format])
  fix \<alpha> :: "('c,'b)assign"
  show "pos_assign \<alpha> \<Longrightarrow> eval_poly \<alpha> (f v) \<ge> eval_poly \<alpha> (g v)" using fgv unfolding poly_ge_def by auto
next
  fix \<alpha> :: "('c,'b)assign"
  assume alpha: "pos_assign \<alpha>"
  show "pos_assign (\<lambda>v. eval_poly \<alpha> (g v))" 
    unfolding pos_assign_def
  proof
    fix x
    show "eval_poly \<alpha> (g x) \<ge> 0"
    using g[of x] unfolding poly_ge_def zero_poly_def using alpha by auto
  qed
next
  fix \<alpha> :: "('c,'b)assign" and x
  assume v: "v \<noteq> x"
  show "pos_assign \<alpha> \<Longrightarrow> eval_poly \<alpha> (f x) = eval_poly \<alpha> (g x)" using fgw[OF v] unfolding poly_ge_def by auto
qed

lemma poly_weak_mono: fixes p :: "('v,'a :: poly_carrier)poly"
  assumes mono: "\<And> v. v \<in> poly_vars p \<Longrightarrow> poly_weak_mono p v"
  shows "poly_weak_mono_all p"
unfolding poly_weak_mono_all_def
proof (intro allI impI)
  fix \<alpha> \<beta> :: "('v,'a)assign"
  assume all: "\<forall> x. \<alpha> x \<ge> \<beta> x"
  assume pos: "pos_assign \<beta>"
  let ?ab = "\<lambda> vs v. if (v \<in> set vs) then \<alpha> v else \<beta> v"
  {
    fix vs :: "'v list"
    assume "set vs \<subseteq> poly_vars p"
    hence "eval_poly (?ab vs) p \<ge> eval_poly \<beta> p"
    proof (induct vs)
      case Nil show ?case by (simp add: ge_refl)
    next
      case (Cons v vs)
      hence subset: "set vs \<subseteq> poly_vars p"  and v: "v \<in> poly_vars p" by auto
      show ?case
      proof (rule ge_trans[OF mono[OF v, unfolded poly_weak_mono_def, rule_format] Cons(1)[OF subset]])
        show "pos_assign (?ab vs)" unfolding pos_assign_def
        proof
          fix x
          from pos[unfolded pos_assign_def] have beta: "\<beta> x \<ge> 0" by simp
          from ge_trans[OF all[rule_format] this] have alpha: "\<alpha> x \<ge> 0" .
          from alpha beta show "?ab vs x \<ge> 0" by auto
        qed
        show "(?ab (v # vs) v) \<ge> (?ab vs v)" using all ge_refl by auto
      next
        fix x
        assume "v \<noteq> x"
        thus "(?ab (v # vs) x) = (?ab vs x)" by simp
      qed
    qed
  }
  from this[of "poly_vars_list p", unfolded poly_vars_list]
  have "eval_poly (\<lambda>v. if v \<in> poly_vars p then \<alpha> v else \<beta> v) p \<ge> eval_poly \<beta> p" by auto
  also have "eval_poly (\<lambda>v. if v \<in> poly_vars p then \<alpha> v else \<beta> v) p = eval_poly \<alpha> p"
    by (rule eval_poly_vars, auto)
  finally
  show "eval_poly \<alpha> p \<ge> eval_poly \<beta> p" .
qed  

lemma poly_weak_mono_all: fixes p :: "('v,'a :: poly_carrier)poly" 
  assumes p: "poly_weak_mono_all p"
  shows "poly_weak_mono p v"
unfolding poly_weak_mono_def
proof (intro allI impI)
  fix \<alpha> \<beta> :: "('v,'a)assign"
  assume all: "\<forall>x. v \<noteq> x \<longrightarrow> \<alpha> x = \<beta> x"
  assume pos: "pos_assign \<beta>"
  assume v: "\<alpha> v \<ge> \<beta> v"
  show "eval_poly \<alpha> p \<ge> eval_poly \<beta> p" 
  proof (rule p[unfolded poly_weak_mono_all_def, rule_format, OF _ pos])
    fix x 
    show "\<alpha> x \<ge> \<beta> x"
    using v all ge_refl[of "\<beta> x"] by auto
  qed
qed

lemma poly_weak_mono_all_pos: 
  fixes p :: "('v,'a :: poly_carrier)poly"
  assumes pos_at_zero: "eval_poly (\<lambda> w. 0) p \<ge> 0"
  and mono: "poly_weak_mono_all p"
  shows "p \<ge>p zero_poly"
unfolding poly_ge_def zero_poly_def
proof (intro allI impI, simp)
  fix  \<alpha> :: "('v,'a)assign"
  assume pos: "pos_assign \<alpha>"
  show "eval_poly \<alpha> p \<ge> 0"
  proof -
    let ?id = "\<lambda> w. poly_of (PVar w)"
    let ?z = "\<lambda> w. zero_poly"
    have "poly_subst ?id p \<ge>p poly_subst ?z p" 
      by (rule poly_weak_mono_all_E[OF mono],  
        simp, simp add: poly_ge_def zero_poly_def pos_assign_def) 
    hence "eval_poly \<alpha> (poly_subst ?id p) \<ge> eval_poly \<alpha> (poly_subst ?z p)" (is "_ \<ge> ?res")
      unfolding poly_ge_def using pos by simp
    also have "?res = eval_poly (\<lambda> w. 0) p" by (simp add: poly_subst zero_poly_def)
    also have "\<dots> \<ge> 0" by (rule pos_at_zero)
    finally show ?thesis by  (simp add: poly_subst)
  qed
qed

context poly_order_carrier
begin

definition poly_strict_mono :: "('v,'a)poly \<Rightarrow> 'v \<Rightarrow> bool" where 
  "poly_strict_mono p v \<equiv> \<forall> (\<alpha> :: ('v,'a)assign) \<beta>. (\<forall> x. (v \<noteq> x \<longrightarrow> \<alpha> x = \<beta> x)) \<longrightarrow> pos_assign \<beta> \<longrightarrow> \<alpha> v \<succ> \<beta> v \<longrightarrow> eval_poly \<alpha> p \<succ> eval_poly \<beta> p"

lemma poly_strict_mono_E: assumes p: "poly_strict_mono p v"
  and fgw: "\<And> w. v \<noteq> w \<Longrightarrow> f w = g w"
  and g: "\<And> w. g w \<ge>p zero_poly" 
  and fgv: "f v >p g v"
  shows "poly_subst f p >p poly_subst g p"
  unfolding poly_gt_def poly_subst
proof (intro allI impI, rule p[unfolded poly_strict_mono_def, rule_format])
  fix \<alpha> :: "('c,'a)assign"
  show "pos_assign \<alpha> \<Longrightarrow> eval_poly \<alpha> (f v) \<succ> eval_poly \<alpha> (g v)" using fgv unfolding poly_gt_def by auto
next
  fix \<alpha> :: "('c,'a)assign"
  assume alpha: "pos_assign \<alpha>"
  show "pos_assign (\<lambda>v. eval_poly \<alpha> (g v))" 
    unfolding pos_assign_def
  proof
    fix x
    show "eval_poly \<alpha> (g x) \<ge> 0"
    using g[of x] unfolding poly_ge_def zero_poly_def using alpha by auto
  qed
next
  fix \<alpha> :: "('c,'a)assign" and x
  assume v: "v \<noteq> x"
  show "pos_assign \<alpha> \<Longrightarrow> eval_poly \<alpha> (f x) = eval_poly \<alpha> (g x)" using fgw[OF v] unfolding poly_ge_def by auto
qed

lemma poly_add_gt_mono: assumes "p1 >p p2" shows "poly_add p1 q >p poly_add p2 q"
using assms unfolding poly_gt_def by (auto simp: field_simps plus_gt_left_mono)

lemma poly_mult_gt_mono: 
  fixes q :: "('v,'a)poly"
  assumes gt: "p1 >p p2" and mono: "q \<ge>p one_poly"
  shows "poly_mult p1 q >p poly_mult p2 q"
proof (unfold poly_gt_def, intro impI allI)
  fix \<alpha> :: "('v,'a)assign"
  assume p: "pos_assign \<alpha>"
  with gt have gt: "eval_poly \<alpha> p1 \<succ> eval_poly \<alpha> p2" unfolding poly_gt_def by simp
  from mono p have one: "eval_poly \<alpha> q \<ge> 1" unfolding poly_ge_def one_poly_def by auto
  show "eval_poly \<alpha> (poly_mult p1 q) \<succ> eval_poly \<alpha> (poly_mult p2 q)"
    using times_gt_mono[OF gt one] by simp
qed
end

subsection {* Degree of polynomials *}

definition monom_degree :: "'v monom \<Rightarrow> nat" where 
  "monom_degree xps \<equiv> listsum (map snd xps)"

definition poly_degree :: "('v,'a) poly \<Rightarrow> nat" where
  "poly_degree p \<equiv> max_list (map (\<lambda> (m,c). monom_degree m) p)"

definition poly_coeff_sum :: "('v,'a :: ordered_ab_semigroup) poly \<Rightarrow> 'a" where
  "poly_coeff_sum p \<equiv> listsum (map (\<lambda> mc. max 0 (snd mc)) p)"

lemma monom_degree: "eval_monom (\<lambda> _. x) m = x ^ monom_degree m"
  unfolding monom_degree_def
proof (induct m)
  case Nil show ?case by simp
next 
  case (Cons mc m)
  thus ?case by (cases mc, auto simp: power_add field_simps)
qed

lemma poly_coeff_sum: "poly_coeff_sum p \<ge> 0"
  unfolding poly_coeff_sum_def
proof (induct p)
  case Nil show ?case by (simp add: ge_refl)
next
  case (Cons mc p)
  have "(\<Sum>mc\<leftarrow>mc # p. max 0 (snd mc)) = max 0 (snd mc) + (\<Sum>mc\<leftarrow>p. max 0 (snd mc))" by auto
  also have "\<dots> \<ge> 0 + 0"
    by (rule ge_trans[OF plus_left_mono plus_right_mono[OF Cons]], auto)
  finally show ?case by simp
qed

lemma poly_degree: assumes x: "x \<ge> (1 :: 'a :: poly_carrier)" 
  shows "poly_coeff_sum p * (x ^ poly_degree p) \<ge> eval_poly (\<lambda> _. x) p"
proof (induct p)
  case Nil show ?case by (simp add: ge_refl poly_degree_def poly_coeff_sum_def)
next
  case (Cons mc p)  
  obtain m c where mc: "mc = (m,c)" by force
  from ge_trans[OF x one_ge_zero] have x0: "x \<ge> 0" .
  have id1: "eval_poly (\<lambda>_. x) (mc # p) = x ^ monom_degree m  * c + eval_poly (\<lambda>_. x) p" unfolding mc by (simp add: monom_degree)
  have id2: "poly_coeff_sum (mc # p) * x ^ poly_degree (mc # p) = 
    x ^ max (monom_degree m) (poly_degree p) * (max 0 c) + poly_coeff_sum p * x ^ max (monom_degree m) (poly_degree p)"
    unfolding poly_coeff_sum_def poly_degree_def by (simp add: mc field_simps)
  show "poly_coeff_sum (mc # p) * x ^ poly_degree (mc # p) \<ge> eval_poly (\<lambda>_. x) (mc # p)"
    unfolding id1 id2
  proof (rule ge_trans[OF plus_left_mono plus_right_mono])
    show "x ^ max (monom_degree m) (poly_degree p) * max 0 c \<ge> x ^ monom_degree m * c"
      by (rule ge_trans[OF times_left_mono[OF _ pow_mono_exp] times_right_mono[OF pow_ge_zero]], insert x x0, auto)
    show "poly_coeff_sum p * x ^ max (monom_degree m) (poly_degree p) \<ge> eval_poly (\<lambda>_. x) p"
      by (rule ge_trans[OF times_right_mono[OF poly_coeff_sum pow_mono_exp[OF x]] Cons], auto)
  qed
qed

lemma poly_degree_bound: assumes x: "x \<ge> (1 :: 'a :: poly_carrier)" 
  and c: "c \<ge> poly_coeff_sum p"
  and d: "d \<ge> poly_degree p"
  shows "c * (x ^ d) \<ge> eval_poly (\<lambda> _. x) p"
  by (rule ge_trans[OF ge_trans[OF 
    times_left_mono[OF pow_ge_zero[OF ge_trans[OF x one_ge_zero]] c]   
    times_right_mono[OF poly_coeff_sum pow_mono_exp[OF x d]]] poly_degree[OF x]])


subsection {* Executable and sufficient criteria to compare polynomials and ensure monotonicity *} 

text {* poly\_split extracts the coefficient for a given monomial and returns additionally the remaining polynomial *}
definition poly_split :: "('v monom) \<Rightarrow> ('v,'a :: zero)poly \<Rightarrow> 'a \<times> ('v,'a)poly" 
  where "poly_split m p \<equiv> case List.extract (\<lambda> (n,_). m =m n) p of None \<Rightarrow> (0,p) | Some (p1,(_,c),p2) \<Rightarrow> (c, p1 @ p2)"

lemma poly_split: assumes "poly_split m p = (c,q)"
  shows "p =p (m,c) # q"
proof (cases "List.extract (\<lambda> (n,_). m =m n) p")
  case None
  with assms have "(c,q) = (0,p)" unfolding poly_split_def by auto
  thus ?thesis unfolding eq_poly_def by auto
next
  case (Some res)
  obtain p1 mc p2 where "res = (p1,mc,p2)" by (cases res, auto)
  with extract_SomeE[OF Some[simplified this]] obtain a m' where p: "p = p1 @ (m',a) # p2" and m': "m =m m'" and res: "res = (p1,(m',a),p2)" by (cases mc, auto)
  from Some res assms have c: "c = a" and q: "q = p1 @ p2" unfolding poly_split_def by auto
  show ?thesis unfolding eq_poly_def by (simp add: p c q eq_monom[OF m'] field_simps)
qed 

lemma poly_split_eval: assumes "poly_split m p = (c,q)" 
  shows "eval_poly \<alpha> p = (eval_monom \<alpha> m * c) + eval_poly \<alpha> q"
using poly_split[OF assms] unfolding eq_poly_def by auto

(* we assume that the polynomial invariant is present, otherwise this check might fail, e.g., on 0 =p 0 + 0 *)
fun check_poly_eq :: "('v,'a :: semiring_0)poly \<Rightarrow> ('v,'a)poly \<Rightarrow> bool"
where "check_poly_eq [] q = (q = [])"
    | "check_poly_eq ((m,c) # p) q = (case List.extract (\<lambda> nd. fst nd =m m) q of
                                         None \<Rightarrow> False
                                       | Some (q1,(_,d),q2) \<Rightarrow> c = d \<and> check_poly_eq p (q1 @ q2))"

lemma check_poly_eq: fixes p :: "('v,'a :: poly_carrier)poly"
  assumes chk: "check_poly_eq p q"
  shows "p =p q" unfolding eq_poly_def
proof
  fix \<alpha>
  from chk show "eval_poly \<alpha> p = eval_poly \<alpha> q"
  proof (induct p arbitrary: q)
    case Nil
    thus ?case by auto
  next
    case (Cons mc p)
    obtain m c where mc: "mc = (m,c)" by (cases mc, auto)
    show ?case
    proof (cases "List.extract (\<lambda> mc. fst mc =m m) q")
      case None
      with Cons(2) show ?thesis unfolding mc by simp
    next
      case (Some res)
      obtain q1 md q2 where "res = (q1,md,q2)" by (cases res, auto)
      with extract_SomeE[OF Some[simplified this]] obtain m' d where q: "q = q1 @ (m',d) # q2" and m': "m' =m m" and res: "res = (q1,(m',d),q2)" 
        by (cases md, auto)
      from Cons(2) Some mc res have rec: "check_poly_eq p (q1 @ q2)" and c: "c = d" by auto
      from Cons(1)[OF rec] have p: "eval_poly \<alpha> p = eval_poly \<alpha> (q1 @ q2)" .
      show ?thesis unfolding mc eval_poly.simps c p q using eq_monom[OF m', of \<alpha>] by (simp add: ac_simps)
    qed
  qed
qed

declare check_poly_eq.simps[simp del]


fun check_poly_ge :: "('v,'a :: ordered_semiring_0)poly \<Rightarrow> ('v,'a)poly \<Rightarrow> bool"
where "check_poly_ge [] q = list_all (\<lambda> (_,d). 0 \<ge> d) q"
    | "check_poly_ge ((m,c) # p) q = (case List.extract (\<lambda> nd. fst nd =m m) q of
                                         None \<Rightarrow> c \<ge> 0 \<and> check_poly_ge p q
                                       | Some (q1,(_,d),q2) \<Rightarrow> c \<ge> d \<and> check_poly_ge p (q1 @ q2))"

lemma check_poly_ge: fixes p :: "('v,'a :: poly_carrier)poly"
  shows "check_poly_ge p q \<Longrightarrow> p \<ge>p q"
proof (induct p arbitrary: q)
  case Nil
  hence "\<forall> (n,d) \<in> set q. 0 \<ge> d" using list_all_iff[of _ q] by auto
  hence "[] \<ge>p q" 
  proof (induct q)
    case Nil thus ?case by (simp)
  next
    case (Cons nd q)
    hence rec: "[] \<ge>p q" by simp
    show ?case
    proof (cases nd)
      case (Pair n d)
      with Cons have ge: "0 \<ge> d" by auto
      show ?thesis 
      proof (simp only: Pair, unfold poly_ge_def, intro allI impI)
        fix \<alpha> :: "('v,'a)assign"
        assume pos: "pos_assign \<alpha>"
        have ge: "0 \<ge> eval_monom \<alpha> n * d"
          using times_right_mono[OF pos_assign_monom[OF pos, of n] ge] by simp
        from rec[unfolded poly_ge_def] pos have ge2: "0 \<ge> eval_poly \<alpha> q" by auto
        show "eval_poly \<alpha> [] \<ge> eval_poly \<alpha> ((n,d) # q)" using ge_trans[OF plus_left_mono[OF ge] plus_right_mono[OF ge2]]
          by simp
      qed
    qed
  qed
  thus ?case by simp
next
  case (Cons mc p)
  obtain m c where mc: "mc = (m,c)" by (cases mc, auto)
  show ?case
  proof (cases "List.extract (\<lambda> mc. fst mc =m m) q")
    case None
    with Cons(2) have rec: "check_poly_ge p q" and c: "c \<ge> 0" using mc by auto
    from Cons(1)[OF rec] have rec: "p \<ge>p q" .
    show ?thesis 
    proof (simp only: mc, unfold poly_ge_def, intro allI impI)
      fix \<alpha> :: "('v,'a)assign"
      assume pos: "pos_assign \<alpha>"
      have ge: "eval_monom \<alpha> m * c \<ge> 0"
        using times_right_mono[OF pos_assign_monom[OF pos, of m] c] by simp
      from rec have pq: "eval_poly \<alpha> p \<ge> eval_poly \<alpha> q" unfolding poly_ge_def using pos by auto
      show "eval_poly \<alpha> ((m,c) # p) \<ge> eval_poly \<alpha> q"
        using ge_trans[OF plus_left_mono[OF ge] plus_right_mono[OF pq]] by simp
    qed
  next
    case (Some res)
    obtain q1 md q2 where "res = (q1,md,q2)" by (cases res, auto)
    with extract_SomeE[OF Some[simplified this]] obtain m' d where q: "q = q1 @ (m',d) # q2" and m': "m' =m m" and res: "res = (q1,(m',d),q2)" 
      by (cases md, auto)
    from Cons(2) Some mc res have rec: "check_poly_ge p (q1 @ q2)" and c: "c \<ge> d" by auto
    from Cons(1)[OF rec] have p: "p \<ge>p q1 @ q2" .
    show ?thesis
    proof (simp only: mc, unfold poly_ge_def, intro allI impI)
      fix \<alpha> :: "('v,'a)assign"
      assume pos: "pos_assign \<alpha>"
      have ge: "eval_monom \<alpha> m * c \<ge> eval_monom \<alpha> m' * d"
        using times_right_mono[OF pos_assign_monom[OF pos, of m] c] 
          eq_monom[OF m', of \<alpha>] by simp
      from p have ge2: "eval_poly \<alpha> p \<ge> eval_poly \<alpha> (q1 @ q2)" unfolding poly_ge_def using pos by auto
      show "eval_poly \<alpha> ((m,c) # p) \<ge> eval_poly \<alpha> q" using ge_trans[OF plus_left_mono[OF ge] plus_right_mono[OF ge2]]
        by (simp add: q field_simps)
    qed
  qed
qed

declare check_poly_ge.simps[simp del]

definition check_poly_weak_mono_all :: "('v,'a :: ordered_semiring_0)poly \<Rightarrow> bool"
where "check_poly_weak_mono_all p \<equiv> list_all (\<lambda> (m,c). c \<ge> 0) p"

lemma check_poly_weak_mono_all: fixes p :: "('v,'a :: poly_carrier)poly"
  assumes "check_poly_weak_mono_all p" shows  "poly_weak_mono_all p"
unfolding poly_weak_mono_all_def
proof (intro allI impI)
  fix f g :: "('v,'a)assign"
  assume fg: "\<forall> x. f x \<ge> g x"
  and pos: "pos_assign g"
  hence fg: "\<And> x. f x \<ge> g x" by auto
  from pos[unfolded pos_assign_def] have g: "\<And> x. g x \<ge> 0" ..
  from assms have "\<And> m c. (m,c) \<in> set p \<Longrightarrow> c \<ge> 0" unfolding check_poly_weak_mono_all_def by (auto simp: list_all_iff)
  thus "eval_poly f p \<ge> eval_poly g p"
  proof (induct p)
    case Nil thus ?case by (simp add: ge_refl)
  next
    case (Cons mc p)
    hence IH: "eval_poly f p \<ge> eval_poly g p" by auto
    show ?case 
    proof (cases mc)
      case (Pair m c)
      with Cons have c: "c \<ge> 0" by auto
      show ?thesis unfolding Pair eval_poly.simps fst_conv snd_conv
      proof (rule ge_trans[OF plus_left_mono[OF times_left_mono[OF c]] plus_right_mono[OF IH]])
        show "eval_monom f m \<ge> eval_monom g m"
          by (rule eval_monom_mono(1)[OF fg g])
      qed
    qed
  qed
qed

lemma check_poly_weak_mono_all_pos: 
  assumes "check_poly_weak_mono_all p" shows  "p \<ge>p zero_poly"
unfolding zero_poly_def
proof (rule check_poly_ge)
  from assms have "\<And> m c. (m,c) \<in> set p \<Longrightarrow> c \<ge> 0" unfolding check_poly_weak_mono_all_def by (auto simp: list_all_iff)
  thus "check_poly_ge p []"
    by (induct p, simp add: check_poly_ge.simps,  clarify, auto simp: check_poly_ge.simps extract_Nil_code)
qed


text {* better check for weak monotonicity for discrete carriers: 
   $p$ is monotone in $v$ if $p(\ldots v+1 \ldots) \geq p(\ldots v \ldots)$ *}
definition check_poly_weak_mono_discrete :: "('v,'a :: poly_carrier)poly \<Rightarrow> 'v \<Rightarrow> bool"
  where "check_poly_weak_mono_discrete p v \<equiv> check_poly_ge (poly_subst (\<lambda> w. poly_of (if w = v then PSum [PNum 1, PVar v] else PVar w)) p) p"

definition check_poly_weak_mono_and_pos :: "bool \<Rightarrow> ('v,'a :: poly_carrier)poly \<Rightarrow> bool"
  where "check_poly_weak_mono_and_pos discrete p \<equiv> 
            if discrete then list_all (\<lambda> v. check_poly_weak_mono_discrete p v) (poly_vars_list p) \<and> eval_poly (\<lambda> w. 0) p \<ge>  0
                        else check_poly_weak_mono_all p"

definition check_poly_weak_anti_mono_discrete :: "('v,'a :: poly_carrier)poly \<Rightarrow> 'v \<Rightarrow> bool"
  where "check_poly_weak_anti_mono_discrete p v \<equiv> check_poly_ge p (poly_subst (\<lambda> w. poly_of (if w = v then PSum [PNum 1, PVar v] else PVar w)) p)"

context poly_order_carrier
begin

lemma check_poly_weak_mono_discrete: 
  fixes v :: 'v and p :: "('v,'a)poly"
  assumes discrete and check: "check_poly_weak_mono_discrete p v"
  shows "poly_weak_mono p v"
unfolding poly_weak_mono_def 
proof (intro allI impI)
  fix f g :: "('v,'a)assign"
  assume fgw: "\<forall> w. (v \<noteq> w \<longrightarrow> f w = g w)"
  and gass: "pos_assign g"
  and v: "f v \<ge> g v"
  from fgw have w: "\<And> w. v \<noteq> w \<Longrightarrow> f w = g w" by auto
  from assms check_poly_ge have ge: "poly_ge (poly_subst (\<lambda> w. poly_of (if w = v then PSum [PNum 1, PVar v] else PVar w)) p) p" (is "poly_ge ?p1 p") unfolding check_poly_weak_mono_discrete_def by blast
  from discrete[OF `discrete` v] obtain k' where id: "f v = ((op + 1)^^k') (g v)" by auto
  show "eval_poly f p \<ge> eval_poly g p"
  proof (cases k')
    case 0
    {
      fix x
      have "f x = g x" using id 0 w by (cases "x = v", auto)
    }
    hence "f = g" ..
    thus ?thesis using ge_refl by simp
  next
    case (Suc k)
    with id have "f v = ((op + 1)^^(Suc k))  (g v)" by simp 
    with w gass show "eval_poly f p \<ge> eval_poly g p"
    proof (induct k arbitrary: f g rule: less_induct)
      case (less k)
      show ?case 
      proof (cases k)
        case 0
        with less have id0: "f v = 1 + g v" by simp
        have id1: "eval_poly f p = eval_poly g ?p1"
        proof (rule eval_poly_subst)
          fix w
          show "f w = eval_poly g (poly_of (if w = v then PSum [PNum 1, PVar v] else PVar w))"
          proof (cases "w = v")
            case True
            show ?thesis by (simp add: True id0 zero_poly_def)
          next
            case False
            with less have "f w = g w" by simp
            thus ?thesis by (simp add: False)
          qed
        qed
        have "eval_poly g ?p1 \<ge> eval_poly g p" using ge less unfolding poly_ge_def by simp
        with id1 show ?thesis by simp
      next
        case (Suc kk)        
        obtain g' where g': "g' = (\<lambda> w. if (w = v) then 1 + g w else g w)" by auto
        have "(1 :: 'a) + g v \<ge> 1 + 0" 
          by (rule plus_right_mono, simp add: less(3)[unfolded pos_assign_def])
        also have "1 + (0 :: 'a) = 1" by simp
        also have "\<dots> \<ge> 0" by (rule one_ge_zero)
        finally have g'pos: "pos_assign g'" using less(3) unfolding pos_assign_def 
          by (simp add: g')
        {
          fix w
          assume "v \<noteq> w"
          hence "f w = g' w"
            unfolding g' by (simp add: less)
        } note w = this
        have eq: "f v = (op + (1 :: 'a) ^^ Suc kk) ((g' v))"
          by (simp add: less(4) g' Suc, rule arg_cong[where f = "op + 1"], induct kk, auto)
        from Suc have kk: "kk < k" by simp
        from less(1)[OF kk w g'pos] eq
        have rec1: "eval_poly f p \<ge> eval_poly g' p" by simp
        { 
          fix w
          assume "v \<noteq> w"
          hence "g' w = g w"
            unfolding g' by simp
        } note w = this
        from Suc have z: "0 < k" by simp
        from less(1)[OF z w less(3)] g'
        have rec2: "eval_poly g' p \<ge> eval_poly g p" by simp
        show ?thesis by (rule ge_trans[OF rec1 rec2])
      qed
    qed
  qed
qed

lemma check_poly_weak_anti_mono_discrete: 
  fixes v :: 'v and p :: "('v,'a)poly"
  assumes discrete and check: "check_poly_weak_anti_mono_discrete p v"
  shows "poly_weak_anti_mono p v"
unfolding poly_weak_anti_mono_def 
proof (intro allI impI)
  fix f g :: "('v,'a)assign"
  assume fgw: "\<forall> w. (v \<noteq> w \<longrightarrow> f w = g w)"
  and gass: "pos_assign g"
  and v: "f v \<ge> g v"
  from fgw have w: "\<And> w. v \<noteq> w \<Longrightarrow> f w = g w" by auto
  from assms check_poly_ge have ge: "poly_ge p (poly_subst (\<lambda> w. poly_of (if w = v then PSum [PNum 1, PVar v] else PVar w)) p)" (is "poly_ge p ?p1") unfolding check_poly_weak_anti_mono_discrete_def by blast
  from discrete[OF `discrete` v] obtain k' where id: "f v = ((op + 1)^^k') (g v)" by auto
  show "eval_poly g p \<ge> eval_poly f p"
  proof (cases k')
    case 0
    {
      fix x
      have "f x = g x" using id 0 w by (cases "x = v", auto)
    }
    hence "f = g" ..
    thus ?thesis using ge_refl by simp
  next
    case (Suc k)
    with id have "f v = ((op + 1)^^(Suc k))  (g v)" by simp 
    with w gass show "eval_poly g p \<ge> eval_poly f p"
    proof (induct k arbitrary: f g rule: less_induct)
      case (less k)
      show ?case 
      proof (cases k)
        case 0
        with less have id0: "f v = 1 + g v" by simp
        have id1: "eval_poly f p = eval_poly g ?p1"
        proof (rule eval_poly_subst)
          fix w
          show "f w = eval_poly g (poly_of (if w = v then PSum [PNum 1, PVar v] else PVar w))"
          proof (cases "w = v")
            case True
            show ?thesis by (simp add: True id0 zero_poly_def)
          next
            case False
            with less have "f w = g w" by simp
            thus ?thesis by (simp add: False)
          qed
        qed
        have "eval_poly g p \<ge> eval_poly g ?p1" using ge less unfolding poly_ge_def by simp
        with id1 show ?thesis by simp
      next
        case (Suc kk)        
        obtain g' where g': "g' = (\<lambda> w. if (w = v) then 1 + g w else g w)" by auto
        have "(1 :: 'a) + g v \<ge> 1 + 0" 
          by (rule plus_right_mono, simp add: less(3)[unfolded pos_assign_def])
        also have "(1 :: 'a) + 0 = 1" by simp
        also have "\<dots> \<ge> 0" by (rule one_ge_zero)
        finally have g'pos: "pos_assign g'" using less(3) unfolding pos_assign_def 
          by (simp add: g')
        {
          fix w
          assume "v \<noteq> w"
          hence "f w = g' w"
            unfolding g' by (simp add: less)
        } note w = this
        have eq: "f v = (op + (1 :: 'a) ^^ Suc kk) ((g' v))"
          by (simp add: less(4) g' Suc, rule arg_cong[where f = "op + 1"], induct kk, auto)
        from Suc have kk: "kk < k" by simp
        from less(1)[OF kk w g'pos] eq
        have rec1: "eval_poly g' p \<ge> eval_poly f p" by simp
        { 
          fix w
          assume "v \<noteq> w"
          hence "g' w = g w"
            unfolding g' by simp
        } note w = this
        from Suc have z: "0 < k" by simp
        from less(1)[OF z w less(3)] g'
        have rec2: "eval_poly g p \<ge> eval_poly g' p" by simp
        show ?thesis by (rule ge_trans[OF rec2 rec1])
      qed
    qed
  qed
qed

lemma check_poly_weak_mono_and_pos: 
  fixes p :: "('v,'a)poly"
  assumes "check_poly_weak_mono_and_pos discrete p"
  shows "poly_weak_mono_all p \<and> (p \<ge>p zero_poly)"
proof (cases discrete)
  case False
  with assms have c: "check_poly_weak_mono_all p" unfolding check_poly_weak_mono_and_pos_def
    by auto
  from check_poly_weak_mono_all[OF c] check_poly_weak_mono_all_pos[OF c] show ?thesis by auto
next
  case True
  with assms have c: "list_all (\<lambda> v. check_poly_weak_mono_discrete p v) (poly_vars_list p)" and g: "eval_poly (\<lambda> w. 0) p \<ge> 0"
    unfolding check_poly_weak_mono_and_pos_def by auto
  have m: "poly_weak_mono_all p"
  proof (rule poly_weak_mono)
    fix v :: 'v
    assume v: "v \<in> poly_vars p"
    show "poly_weak_mono p v"
      by (rule check_poly_weak_mono_discrete[OF True], insert c[unfolded list_all_iff] v, auto)  
  qed
  have m': "poly_weak_mono_all  p"
  proof (rule poly_weak_mono)
    fix v :: 'v
    assume v: "v \<in> poly_vars p"
    show "poly_weak_mono p v"
      by (rule check_poly_weak_mono_discrete[OF True], insert c[unfolded list_all_iff] v, auto) 
  qed
  from poly_weak_mono_all_pos[OF g m'] m show ?thesis by auto
qed

end

lemma monom_vars_eval_monom: "\<lbrakk>\<And> x. x \<in> monom_vars m \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> eval_monom f m = eval_monom g m"
  by (induct m, auto)

definition check_poly_weak_mono :: "('v,'a :: ordered_semiring_0)poly \<Rightarrow> 'v \<Rightarrow> bool"
  where "check_poly_weak_mono p v \<equiv> list_all (\<lambda> (m,c). c \<ge> 0 \<or> v \<notin> monom_vars m) p"

lemma check_poly_weak_mono: fixes p :: "('v,'a :: poly_carrier)poly"
  assumes "check_poly_weak_mono p v" shows  "poly_weak_mono p v"
unfolding poly_weak_mono_def
proof (intro allI impI)
  fix f g :: "('v,'a)assign"
  assume "\<forall> x. v \<noteq> x \<longrightarrow> f x = g x"
  and pos: "pos_assign g" 
  and ge: "f v \<ge> g v"
  hence fg: "\<And> x. v \<noteq> x \<Longrightarrow> f x = g x" by auto
  from pos[unfolded pos_assign_def] have g: "\<And> x. g x \<ge> 0" ..
  from assms have "\<And> m c. (m,c) \<in> set p \<Longrightarrow> c \<ge> 0 \<or> v \<notin> monom_vars m" unfolding check_poly_weak_mono_def by (auto simp: list_all_iff)
  thus "eval_poly f p \<ge> eval_poly g p"
  proof (induct p)
    case Nil thus ?case by (simp add: ge_refl)
  next
    case (Cons mc p)
    hence IH: "eval_poly f p \<ge> eval_poly g p" by auto
    obtain m c where mc: "mc = (m,c)" by force
    with Cons have c: "c \<ge> 0 \<or> v \<notin> monom_vars m" by auto
    show ?case unfolding mc eval_poly.simps fst_conv snd_conv
    proof (rule ge_trans[OF plus_left_mono plus_right_mono[OF IH]])
      from c show "eval_monom f m * c \<ge> eval_monom g m * c"
      proof
        assume c: "c \<ge> 0"
        show ?thesis
        proof (rule times_left_mono[OF c], rule eval_monom_mono(1)[OF _ g])
          fix x
          show "f x \<ge> g x" using ge fg[of x] by (cases "x = v", auto simp: ge_refl)
        qed
      next
        assume v: "v \<notin> monom_vars m"
        have "eval_monom f m = eval_monom g m"
          by (rule monom_vars_eval_monom, insert fg v, auto)
        thus ?thesis by (simp add: ge_refl)        
      qed
    qed
  qed
qed

definition check_poly_weak_mono_smart :: "bool \<Rightarrow> ('v,'a :: poly_carrier)poly \<Rightarrow> 'v \<Rightarrow> bool"
  where "check_poly_weak_mono_smart discrete \<equiv> if discrete then check_poly_weak_mono_discrete else check_poly_weak_mono"

lemma (in poly_order_carrier) check_poly_weak_mono_smart: fixes p :: "('v,'a :: poly_carrier)poly"
  shows "check_poly_weak_mono_smart discrete p v \<Longrightarrow> poly_weak_mono p v"
  unfolding check_poly_weak_mono_smart_def
  using check_poly_weak_mono check_poly_weak_mono_discrete by (cases discrete, auto)

definition check_poly_weak_anti_mono :: "('v,'a :: ordered_semiring_0)poly \<Rightarrow> 'v \<Rightarrow> bool"
  where "check_poly_weak_anti_mono p v \<equiv> list_all (\<lambda> (m,c). 0 \<ge> c \<or> v \<notin> monom_vars m) p"

lemma check_poly_weak_anti_mono: fixes p :: "('v,'a :: poly_carrier)poly"
  assumes "check_poly_weak_anti_mono p v" shows  "poly_weak_anti_mono p v"
unfolding poly_weak_anti_mono_def
proof (intro allI impI)
  fix f g :: "('v,'a)assign"
  assume "\<forall> x. v \<noteq> x \<longrightarrow> f x = g x"
  and pos: "pos_assign g" 
  and ge: "f v \<ge> g v"
  hence fg: "\<And> x. v \<noteq> x \<Longrightarrow> f x = g x" by auto
  from pos[unfolded pos_assign_def] have g: "\<And> x. g x \<ge> 0" ..
  from assms have "\<And> m c. (m,c) \<in> set p \<Longrightarrow> 0 \<ge> c \<or> v \<notin> monom_vars m" unfolding check_poly_weak_anti_mono_def by (auto simp: list_all_iff)
  thus "eval_poly g p \<ge> eval_poly f p"
  proof (induct p)
    case Nil thus ?case by (simp add: ge_refl)
  next
    case (Cons mc p)
    hence IH: "eval_poly g p \<ge> eval_poly f p" by auto
    obtain m c where mc: "mc = (m,c)" by force
    with Cons have c: "0 \<ge> c \<or> v \<notin> monom_vars m" by auto
    show ?case unfolding mc eval_poly.simps fst_conv snd_conv
    proof (rule ge_trans[OF plus_left_mono plus_right_mono[OF IH]])
      from c show "eval_monom g m * c \<ge> eval_monom f m * c"
      proof
        assume c: "0 \<ge> c"
        show ?thesis
        proof (rule times_left_anti_mono[OF eval_monom_mono(1)[OF _ g] c])
          fix x
          show "f x \<ge> g x" using ge fg[of x] by (cases "x = v", auto simp: ge_refl)
        qed
      next
        assume v: "v \<notin> monom_vars m"
        have "eval_monom f m = eval_monom g m"
          by (rule monom_vars_eval_monom, insert fg v, auto)
        thus ?thesis by (simp add: ge_refl)        
      qed
    qed
  qed
qed

definition check_poly_weak_anti_mono_smart :: "bool \<Rightarrow> ('v,'a :: poly_carrier)poly \<Rightarrow> 'v \<Rightarrow> bool"
  where "check_poly_weak_anti_mono_smart discrete \<equiv> if discrete then check_poly_weak_anti_mono_discrete else check_poly_weak_anti_mono"

lemma (in poly_order_carrier) check_poly_weak_anti_mono_smart: fixes p :: "('v,'a :: poly_carrier)poly"
  shows "check_poly_weak_anti_mono_smart discrete p v \<Longrightarrow> poly_weak_anti_mono p v"
  unfolding check_poly_weak_anti_mono_smart_def
  using check_poly_weak_anti_mono[of p v] check_poly_weak_anti_mono_discrete[of p v] 
  by (cases discrete, auto)

definition check_poly_gt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('v,'a :: ordered_semiring_0)poly \<Rightarrow> ('v,'a)poly \<Rightarrow> bool"
where "check_poly_gt gt p q \<equiv> let (a1,p1) = poly_split [] p; (b1,q1) = poly_split [] q in gt a1 b1 \<and> check_poly_ge p1 q1"

definition check_monom_strict_mono :: "bool \<Rightarrow> 'v monom \<Rightarrow> 'v \<Rightarrow> bool"
  where "check_monom_strict_mono pm m v \<equiv> m \<noteq> [] \<and> tl m = [] \<and> fst (hd m) = v \<and> (\<lambda> p. if pm then 1 \<le> p else p = 1) (snd (hd m))"

definition check_poly_strict_mono :: "bool \<Rightarrow> ('v,'a :: poly_carrier)poly \<Rightarrow> 'v \<Rightarrow> bool"
  where "check_poly_strict_mono pm p v \<equiv> list_ex (\<lambda> (m,c). (c \<ge> 1) \<and> check_monom_strict_mono pm m v) p"

definition check_poly_strict_mono_discrete :: "('a :: poly_carrier \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('v,'a)poly \<Rightarrow> 'v \<Rightarrow> bool"
  where "check_poly_strict_mono_discrete gt p v \<equiv> check_poly_gt gt (poly_subst (\<lambda> w. poly_of (if w = v then PSum [PNum 1, PVar v] else PVar w)) p) p "

definition check_poly_strict_mono_smart :: "bool \<Rightarrow> bool \<Rightarrow> ('a :: poly_carrier \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('v,'a)poly \<Rightarrow> 'v \<Rightarrow> bool"
  where "check_poly_strict_mono_smart discrete pm gt p v \<equiv> 
            if discrete then check_poly_strict_mono_discrete gt p v else check_poly_strict_mono pm p v"


context poly_order_carrier
begin
lemma check_monom_strict_mono: fixes \<alpha> \<beta> :: "('v,'a)assign" and v :: 'v and m :: "'v monom"
  assumes check: "check_monom_strict_mono power_mono m v"
  and gt: "\<alpha> v \<succ> \<beta> v"
  and ge: "\<beta> v \<ge> 0"
  shows "eval_monom \<alpha> m \<succ> eval_monom \<beta> m"
proof (cases power_mono)
  case False
  with check have "m = [(v,1)]" unfolding check_monom_strict_mono_def by (cases m, cases "tl m", cases "hd m", auto)
  with gt show ?thesis by (auto)
next
  case True
  with check obtain n where m: "m = [(v,n)]" and n: "1 \<le> n" unfolding check_monom_strict_mono_def by (cases m, cases "tl m", cases "hd m", auto)
  from power_mono[OF True gt ge n] m show ?thesis by auto
qed

lemma check_poly_strict_mono: 
  assumes check1: "check_poly_strict_mono power_mono p v"
  and check2: "check_poly_weak_mono_all p"
  shows "poly_strict_mono p v"
unfolding poly_strict_mono_def
proof (intro allI impI)
  fix f g :: "('b,'a)assign"
  assume fgw: "\<forall> w. (v \<noteq> w \<longrightarrow> f w = g w)"
  and pos: "pos_assign g"
  and fgv: "f v \<succ> g v"
  from pos[unfolded pos_assign_def] have g: "\<And> x. g x \<ge> 0" ..
  {
    fix w
    have "f w \<ge> g w"
    proof (cases "v = w")
      case False
      with fgw ge_refl show ?thesis by auto
    next
      case True
      from fgv[unfolded True] show ?thesis by (rule gt_imp_ge)
    qed
  } note fgw2 = this
  let ?e = "eval_poly"
  show "?e f p \<succ> ?e g p"
    using check1[unfolded check_poly_strict_mono_def, simplified list_ex_iff]
      check2[unfolded check_poly_weak_mono_all_def, simplified list_all_iff, THEN bspec]
  proof (induct p)
    case Nil thus ?case by simp
  next
    case (Cons mc p)
    obtain m c where mc: "mc = (m,c)" by (cases mc, auto)
    show ?case 
    proof (cases "c \<ge> 1 \<and> check_monom_strict_mono power_mono m v")
      case True
      hence c: "c \<ge> 1" and m: "check_monom_strict_mono power_mono m v" by blast+
      from times_gt_mono[OF check_monom_strict_mono[OF m, of f g, OF fgv g] c]
      have gt: "eval_monom f m * c \<succ> eval_monom g m * c" .
      from Cons(3) have "check_poly_weak_mono_all p" unfolding check_poly_weak_mono_all_def list_all_iff by auto
      from check_poly_weak_mono_all[OF this, unfolded poly_weak_mono_all_def, rule_format, OF fgw2 pos]
      have ge: "?e f p \<ge> ?e g p" .
      from compat2[OF plus_gt_left_mono[OF gt] plus_right_mono[OF ge]]
      show ?thesis unfolding mc by simp
    next
      case False
      with Cons(2) mc have "\<exists> mc \<in> set p. (\<lambda> (m,c). c \<ge> 1 \<and> check_monom_strict_mono power_mono m v) mc" by auto
      from Cons(1)[OF this] Cons(3) have rec: "?e f p \<succ> ?e g p" by simp
      from Cons(3) mc have c: "c \<ge> 0" by auto
      from times_left_mono[OF c eval_monom_mono(1)[OF fgw2 g]] 
      have ge: "eval_monom f m * c \<ge> eval_monom g m * c" .
      from compat2[OF plus_gt_left_mono[OF rec] plus_right_mono[OF ge]]
      show ?thesis by (simp add: mc field_simps)
    qed
  qed 
qed     
      

lemma check_poly_gt: 
  fixes p :: "('v,'a)poly"
  assumes "check_poly_gt gt p q" shows "p >p q"
proof -
  obtain a1 p1 where p: "poly_split [] p = (a1,p1)" by (cases "poly_split [] p", auto)
  obtain b1 q1 where q: "poly_split [] q = (b1,q1)" by (cases "poly_split [] q", auto)
  from p q assms have gt: "a1 \<succ> b1" and ge: "p1 \<ge>p q1" unfolding check_poly_gt_def using check_poly_ge[of p1 q1]  by auto
  show ?thesis
  proof (unfold poly_gt_def, intro impI allI)
    fix \<alpha> :: "('v,'a)assign"
    assume "pos_assign \<alpha>"
    with ge have ge: "eval_poly \<alpha> p1 \<ge> eval_poly \<alpha> q1" unfolding poly_ge_def by simp
    from plus_gt_left_mono[OF gt] compat[OF plus_left_mono[OF ge]] have gt: "a1 + eval_poly \<alpha> p1 \<succ> b1 + eval_poly \<alpha> q1" by (force simp: field_simps)
    show "eval_poly \<alpha> p \<succ> eval_poly \<alpha> q"
      by (simp add: poly_split[OF p, unfolded eq_poly_def] poly_split[OF q, unfolded eq_poly_def] gt)
  qed
qed

lemma check_poly_strict_mono_discrete: 
  fixes v :: 'v and p :: "('v,'a)poly"
  assumes discrete and check: "check_poly_strict_mono_discrete gt p v"
  shows "poly_strict_mono p v"
unfolding poly_strict_mono_def 
proof (intro allI impI)
  fix f g :: "('v,'a)assign"
  assume fgw: "\<forall> w. (v \<noteq> w \<longrightarrow> f w = g w)"
  and gass: "pos_assign g"
  and v: "f v \<succ> g v"
  from gass have g: "\<And> x. g x \<ge> 0" unfolding pos_assign_def ..
  from fgw have w: "\<And> w. v \<noteq> w \<Longrightarrow> f w = g w" by auto
  from assms check_poly_gt have gt: "poly_gt (poly_subst (\<lambda> w. poly_of (if w = v then PSum [PNum 1, PVar v] else PVar w)) p) p" (is "poly_gt ?p1 p") unfolding check_poly_strict_mono_discrete_def by blast
  from discrete[OF `discrete` gt_imp_ge[OF v]] obtain k' where id: "f v = ((op + 1)^^k') (g v)" by auto
  {
    assume "k' = 0"
    from v[unfolded id this] have "g v \<succ> g v" by simp
    hence False using SN g[of v] unfolding SN_defs by auto
  }
  with id obtain k where id: "f v = ((op + 1)^^(Suc k)) (g v)" by (cases k', auto)
  with w gass
  show "eval_poly f p \<succ> eval_poly g p"
  proof (induct k arbitrary: f g rule: less_induct)
    case (less k)
    show ?case
    proof (cases k)
      case 0
      with less(4) have id0: "f v = 1 + g v" by simp
      have id1: "eval_poly f p = eval_poly g ?p1"
      proof (rule eval_poly_subst)
        fix w
        show "f w = eval_poly g (poly_of (if w = v then PSum [PNum 1, PVar v] else PVar w))"
        proof (cases "w = v")
          case True
          show ?thesis by (simp add: True id0 zero_poly_def)
        next
          case False
          with less have "f w = g w" by simp
          thus ?thesis by (simp add: False)
        qed
      qed
      have "eval_poly g ?p1 \<succ> eval_poly g p" using gt less unfolding poly_gt_def by simp
      with id1 show ?thesis by simp
    next
      case (Suc kk)        
      obtain g' where g': "g' = (\<lambda> w. if (w = v) then 1 + g w else g w)" by auto
      have "(1 :: 'a) + g v \<ge> 1 + 0" 
        by (rule plus_right_mono, simp add: less(3)[unfolded pos_assign_def])
      also have "(1 :: 'a) + 0 = 1" by simp
      also have "\<dots> \<ge> 0" by (rule one_ge_zero)
      finally have g'pos: "pos_assign g'" using less(3) unfolding pos_assign_def 
        by (simp add: g')
      {
        fix w
        assume "v \<noteq> w"
        hence "f w = g' w"
          unfolding g' by (simp add: less)
      } note w = this
      have eq: "f v = (op + (1 :: 'a) ^^ Suc kk) ((g' v))"
        by (simp add: less(4) g' Suc, rule arg_cong[where f = "op + 1"], induct kk, auto)
      from Suc have kk: "kk < k" by simp
      from less(1)[OF kk w g'pos] eq
      have rec1: "eval_poly f p \<succ> eval_poly g' p" by simp
      { 
        fix w
        assume "v \<noteq> w"
        hence "g' w = g w"
          unfolding g' by simp
      } note w = this
      from Suc have z: "0 < k" by simp
      from less(1)[OF z w less(3)] g'
      have rec2: "eval_poly g' p \<succ> eval_poly g p" by simp
      show ?thesis by (rule gt_trans[OF rec1 rec2])
    qed
  qed
qed

lemma check_poly_strict_mono_smart: 
  assumes check1: "check_poly_strict_mono_smart discrete power_mono gt p v"
  and check2: "check_poly_weak_mono_and_pos discrete p"
  shows "poly_strict_mono p v"
proof (cases discrete)
  case True
  with check1[unfolded check_poly_strict_mono_smart_def]
    check_poly_strict_mono_discrete[OF True]
  show ?thesis by auto
next
  case False
  from check_poly_strict_mono[OF check1[unfolded check_poly_strict_mono_smart_def, simplified False, simplified]]
    check2[unfolded check_poly_weak_mono_and_pos_def, simplified False, simplified]
  show ?thesis by auto
qed

end

end
