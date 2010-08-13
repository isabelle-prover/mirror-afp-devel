(*  Title:       Executable multivariate polynomials
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 Ren√\<copyright> Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and Ren√\<copyright> Thiemann
    License:	 LGPL
*)

(*
Copyright 2010 Christian Sternagel, Ren√\<copyright> Thiemann

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
header {* Polynomials *}

theory Polynomial
imports SN_Orders Util

begin

subsection {*
Polynomials represented as trees
*}
datatype ('v,'a)tpoly = PVar 'v | PNum 'a | PSum "('v,'a)tpoly list" | PMult "('v,'a)tpoly list"

types ('v,'a)assign = "'v \<Rightarrow> 'a"

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


types 'v monom = "('v \<times> nat)list" 
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
fun eq_monom :: "'v monom \<Rightarrow> 'v monom \<Rightarrow> bool" (infix "=m" 51)
where "[] =m n = (n = [])" 
  |   "(x,p) # m =m n = (case extract (\<lambda> yq. fst yq = x) n of
                           None \<Rightarrow> False
                         | Some (n1,(_,q),n2) \<Rightarrow> p = q \<and> m =m (n1 @ n2))"

lemma eq_monom_refl: "m =m m"
proof (induct m, simp)
  case (Cons xp m)
  show ?case 
  proof (cases xp)
    case (Pair x p)
    show ?thesis
      by (simp add: Pair Cons)
  qed
qed

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
  proof (cases n, simp)
    case (Cons yp nn)
    obtain y p where yp: "yp = (y,p)" by (cases yp, auto)
    with Cons Nil(2)[unfolded monom_inv_def] have p: "0 < p" by auto
    show ?thesis by (simp add: Cons, rule exI[of _ y], simp add: sum_var_list_def yp p)
  qed
next
  case (Cons xp m)
  obtain x p where xp: "xp = (x,p)" by (cases xp, auto)
  with Cons(2) have p: "0 < p" and x: "x \<notin> fst ` set m" and m: "monom_inv m" unfolding monom_inv_def by auto
  show ?case 
  proof (cases "extract (\<lambda> yq. fst yq = x) n")
    case None
    from extract_None[OF this] have not1: "x \<notin> fst ` set n" by auto
    show ?thesis
      by (simp add: xp Cons None, rule exI[of _ x], simp add: sum_var_list_not[OF not1], simp add: sum_var_list_def p)
  next
    case (Some res)
    obtain n1 yq n2 where "res = (n1,yq,n2)" by (cases res, auto)
    then obtain y q where "res = (n1,(y,q),n2)" by (cases yq, auto)
    with extract_Some[OF Some[simplified this]] have n: "n = n1 @ (x,q) # n2" and res: "res = (n1,(x,q),n2)"  by auto
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
proof (induct m arbitrary: n, simp)
  case (Cons xp m) note mCons = this
  show ?case
  proof (cases xp)
    case (Pair x p)
    show ?thesis 
    proof (cases "extract (\<lambda> yq. fst yq = x) n")
      case None
      with Cons Pair show ?thesis by auto
    next
      case (Some res)
      obtain n1 yq n2 where "res = (n1,yq,n2)" by (cases res, auto)
      then obtain y q where res: "res = (n1,(y,q),n2)" by (cases yq, auto)
      from extract_Some[OF Some[simplified res]] mCons(2)  Some Pair res have n: "n = n1 @ (x,p) # n2" and rec: "m =m (n1 @ n2)" by auto
      show ?thesis by (simp add: Pair mCons(1)[OF rec] n field_simps)
    qed
  qed
qed

text {*
  equality of monomials is also a complete for several carriers, e.g. the naturals, integers, where $x^p = x^q$ implies $p = q$.
  note that it is not complete for carriers like the Booleans where e.g. $x^{Suc(m)} = x^{Suc(n)}$ for all $n,m$.
*}
lemma eq_monom_inv: 
  fixes m :: "'v monom"
  assumes exp_inject: "\<And> p q :: nat. \<exists> base :: 'a :: poly_carrier. base^p = base^q \<Longrightarrow> p = q" and m: "monom_inv m" and n: "monom_inv n" shows "(m =m n) = (\<forall> \<alpha> :: ('v,'a :: poly_carrier)assign. eval_monom \<alpha> m = eval_monom \<alpha> n)"
proof(intro iffI allI, rule eq_monom, simp)
  assume "\<forall> \<alpha> :: ('v,'a :: poly_carrier)assign. eval_monom \<alpha> m = eval_monom \<alpha> n"
  with m n show "m =m n"
  proof (induct m arbitrary: n)
    case Nil
    show ?case 
    proof (cases n, simp)
      case (Cons yq nn)
      with Nil obtain y q where yq: "yq = (y,q)" and "1 \<le> q" by (cases yq, auto simp: monom_inv_def)
      then obtain qq where q: "q = Suc (qq)" by (cases q, auto)
      from Nil(3) have "1 = eval_monom (\<lambda> x. 0 :: 'a) n" (is "?one = _") by simp
      also have "\<dots> = 0" by (simp add: Cons yq q)
      finally show ?thesis by simp
    qed
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
        proof (induct m, simp)
          case (Cons yp m)
          thus ?case 
            by (cases yp, cases "fst yp = x", auto)
        qed
      } note ass = this
      from Cons(2)[unfolded Pair] obtain pp where p: "p = Suc pp" and xm: "x \<notin> fst ` (set m)" unfolding monom_inv_def by (cases p, auto)
      from ass[OF xm] have "\<And> v. eval_monom (?ass v) (xp # m) = v * v^pp" by (simp add: Pair p)
      with Cons(4) have eval: "\<And> v. eval_monom (?ass v) n = v * v^pp" by auto
      show ?thesis 
      proof (cases "extract (\<lambda> yq. fst yq = x) n")
        case None
        from extract_None[OF this] ass[of n] have "\<And> v. eval_monom (?ass v) n = 1" by auto
        from this[of 0] eval[of 0] show ?thesis by simp
      next
        case (Some res)
        obtain n1 yq n2 where "res = (n1,yq,n2)" by (cases res, auto)
        then obtain y q where "res = (n1,(y,q),n2)" by (cases yq, auto)        
        from extract_Some[OF Some[simplified this]] mCons(2)  Some Pair this have n: "n = n1 @ (x,q) # n2" and res: "res = (n1,(x,q),n2)" by auto
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
qed    

declare eq_monom.simps[simp del]

abbreviation monom_vars :: "'v monom \<Rightarrow> 'v set"
  where "monom_vars m \<equiv> fst ` set m"

fun monom_mult :: "'v monom \<Rightarrow> 'v monom \<Rightarrow> 'v monom"
where "monom_mult [] n = n"
  |   "monom_mult ((x,p) # m) n = (case extract (\<lambda> yq. fst yq = x) n of
                           None \<Rightarrow> (x,p) # monom_mult m n 
                         | Some (n1,(_,q),n2) \<Rightarrow> (x,p+q) # monom_mult m (n1 @ n2))"

lemma monom_mult_vars: "monom_vars (monom_mult m1 m2) = monom_vars m1 \<union> monom_vars m2"
proof (induct m1 arbitrary: m2, simp)
  case (Cons xp m) note mCons = this
  show ?case
  proof (cases xp)
    case (Pair x p)
    show ?thesis 
    proof (cases "extract (\<lambda> yq. fst yq = x) m2")
      case None
      with Cons Pair show ?thesis by auto 
    next
      case (Some res)
      obtain n1 yq n2 where "res = (n1,yq,n2)" by (cases res, auto)
      then obtain y q where res: "res = (n1,(y,q),n2)" by (cases yq, auto)
      from extract_Some[OF Some[simplified res]] Some Pair res have m2: "m2 = n1 @ (x,q) # n2"
        and rec: "monom_mult (xp # m) m2 = (x, p+q) # monom_mult m (n1 @ n2)" by auto
      show ?thesis by (simp only: rec, simp add: mCons Pair m2)
    qed
  qed
qed


lemma monom_mult_inv: "monom_inv m1 \<Longrightarrow> monom_inv m2 \<Longrightarrow> monom_inv (monom_mult m1 m2)"
proof (induct m1 arbitrary: m2, simp add: monom_inv_def)
  case (Cons xp m1)
  obtain x p where xp: "xp = (x,p)" by (cases xp) auto
  from xp Cons(2) have m1: "monom_inv m1" and x: "x \<notin> monom_vars m1" and p: "1 \<le> p" by (auto simp: monom_inv_def)
  show ?case 
  proof (cases "extract (\<lambda> yq. fst yq = x) m2")
    case None
    from extract_None[OF this] have "x \<notin> monom_vars m2" by auto
    from x this have x: "x \<notin> monom_vars (monom_mult m1 m2)" by (simp add: monom_mult_vars)
    with None Cons(1)[OF m1 Cons(3)] x p xp show ?thesis by (auto simp: monom_inv_def)
  next
    case (Some res)
    obtain n1 yq n2 where "res = (n1,yq,n2)" by (cases res, auto)
    then obtain y q where res: "res = (n1,(y,q),n2)" by (cases yq, auto)
    from extract_Some[OF Some[simplified res]] Some xp res have m2: "m2 = n1 @ (x,q) # n2"
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
  shows "monom_mult m m1 =m monom_mult m m2 \<Longrightarrow> m1 =m m2"
proof (simp add: eq_monom_sum_var_list[OF m1 m2] eq_monom_sum_var_list[OF monom_mult_inv[OF m m1] monom_mult_inv[OF m m2]], intro allI)
  fix x
  {
    fix n 
    have "sum_var_list (monom_mult m n) x = sum_var_list m x + sum_var_list n x"
    proof (induct m arbitrary: n, simp add: sum_var_list_def)
      case (Cons yp m)
      obtain y p where yp: "yp = (y,p)" by (cases yp, auto)
      hence id: "sum_var_list (yp # m) x = (if x = y then p else 0) + sum_var_list m x" unfolding sum_var_list_def by auto
      show ?case
      proof (cases "extract (\<lambda> zq. fst zq = y) n")
        case None
        have "sum_var_list (monom_mult (yp # m) n) x = (if x = y then p else 0) + sum_var_list (monom_mult m n) x"
          by (simp add: yp None sum_var_list_def)
        thus ?thesis
          by (simp add: Cons id)
      next
        case (Some res)
        obtain n1 zq n2 where "res = (n1,zq,n2)" by (cases res, auto)
        then obtain z q where res: "res = (n1,(z,q),n2)" by (cases zq, auto)
        from extract_Some[OF Some[simplified res]] Some res yp have n: "n = n1 @ (y,q) # n2"
          and rec: "sum_var_list (monom_mult (yp # m) n) x  = (if x = y then p+q else 0) + sum_var_list (monom_mult m (n1 @ n2)) x" 
          unfolding sum_var_list_def by auto
        show ?thesis
          by (simp only: rec Cons id, simp add: n sum_var_list_def)
      qed
    qed
  } note main = this
  assume "\<forall> x. sum_var_list (monom_mult m m1) x = sum_var_list (monom_mult m m2) x"
  from spec[OF this, of x, simplified main]
  show "sum_var_list m1 x = sum_var_list m2 x"
    by auto
qed


lemma monom_mult[simp]: "eval_monom \<alpha> (monom_mult m n) = eval_monom \<alpha> m * eval_monom \<alpha> n"
proof (induct m arbitrary: n, simp)
  case (Cons xp m) note mCons = this
  show ?case
  proof (cases xp)
    case (Pair x p)
    show ?thesis 
    proof (cases "extract (\<lambda> yq. fst yq = x) n")
      case None
      with Cons Pair show ?thesis by (auto simp: field_simps)
    next
      case (Some res)
      obtain n1 yq n2 where "res = (n1,yq,n2)" by (cases res, auto)
      then obtain y q where res: "res = (n1,(y,q),n2)" by (cases yq, auto)
      from extract_Some[OF Some[simplified res]] Some Pair res have n: "n = n1 @ (x,q) # n2" 
        and rec: "monom_mult (xp # m) n = (x, p+q) # monom_mult m (n1 @ n2)" by auto
      show ?thesis by (simp only: rec, simp add: Pair mCons[of "n1 @ n2"] n field_simps power_add)
    qed
  qed
qed

declare monom_mult.simps[simp del]

text {*
Polynomials are represented with as sum of monomials multiplied by some coefficient 
*}
types ('v,'a)poly = "('v monom \<times> 'a)list"

text {*
The polynomials we construct satisfy the following invariants:
\begin{itemize}
\item 
   all monomials satisfy their invariant
\item all coefficients are non-zero
\item no two equivalent monomials occur in the list 
\end{itemize}
*}


definition poly_inv :: "('v,'a :: zero)poly \<Rightarrow> bool"
  where "poly_inv p \<equiv> (\<forall> (m,c) \<in> set p. monom_inv m \<and> c \<noteq> 0) \<and> distinct_eq (\<lambda> (m1,_) (m2,_). m1 =m m2) p" 


abbreviation eval_monomc where "eval_monomc \<alpha> mc \<equiv> eval_monom \<alpha> (fst mc) * (snd mc)"

fun eval_poly :: "('v,'a :: comm_semiring_1)assign \<Rightarrow> ('v,'a)poly \<Rightarrow> 'a"
where "eval_poly \<alpha> [] = 0"
   |  "eval_poly \<alpha> (mc # p) = eval_monomc \<alpha> mc + eval_poly \<alpha> p"


fun poly_add :: "('v,'a)poly \<Rightarrow> ('v,'a :: semiring_0)poly \<Rightarrow> ('v,'a)poly"
where "poly_add [] q = q"
   |  "poly_add ((m,c) # p) q = (case extract (\<lambda> mc. fst mc =m m) q of
                                None \<Rightarrow> (m,c) # poly_add p q
                              | Some (q1,(_,d),q2) \<Rightarrow> if (c+d = 0) then poly_add p (q1 @ q2) else (m,c+d) # poly_add p (q1 @ q2))"

lemma eval_poly_append[simp]: "eval_poly \<alpha> (mc1 @ mc2) = eval_poly \<alpha> mc1 + eval_poly \<alpha> mc2"
  by (induct mc1, auto simp: field_simps)


abbreviation poly_monoms :: "('v,'a)poly \<Rightarrow> 'v monom set"
  where "poly_monoms p \<equiv> fst ` set p"

lemma poly_add_monoms: "poly_monoms (poly_add p1 p2) \<subseteq> poly_monoms p1 \<union> poly_monoms p2"
proof (induct p1 arbitrary: p2, simp)
  case (Cons mc p)
  obtain m c where mc: "mc = (m,c)" by (cases mc, auto)
  hence m: "m \<in> poly_monoms (mc # p1)" by auto
  show ?case
  proof (cases "extract (\<lambda> nd. fst nd =m m) p2")
    case None
    with Cons m show ?thesis by (auto simp: mc)
  next
    case (Some res)
    obtain q1 md q2 where res: "res = (q1,md,q2)" by (cases res, auto)
    from extract_Some[OF Some[simplified res]] res obtain m' d where q: "p2 = q1 @ (m',d) # q2" and res: "res = (q1,(m',d),q2)" and mm': "m' =m m" by (cases md, auto)
    show ?thesis
      by (simp add: mc Some res, rule subset_trans[OF Cons[of "q1 @ q2"]], auto simp: q)
  qed
qed 
  

lemma poly_add_inv: "poly_inv p \<Longrightarrow> poly_inv q \<Longrightarrow> poly_inv (poly_add p q)"
proof (induct p arbitrary: q, simp)
  case (Cons mc p)
  obtain m c where mc: "mc = (m,c)" by (cases mc, auto)
  with Cons(2) have p: "poly_inv p" and m: "monom_inv m" and c: "c \<noteq> 0" and mp: "\<forall> (mm,dd) \<in> set p. (\<not> mm =m m)" unfolding poly_inv_def by auto
  show ?case
  proof (cases "extract (\<lambda> mc. fst mc =m m) q")
    case None
    from extract_None[OF this] have mq: "\<forall> (mm,dd) \<in> set q. \<not> mm =m m" by auto
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
    from extract_Some[OF Some[simplified res]] res obtain m' d where q: "q = q1 @ (m',d) # q2" and res: "res = (q1,(m',d),q2)" and mm': "m' =m m" by (cases md, auto)
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
qed
    


lemma poly_add[simp]: "eval_poly \<alpha> (poly_add p q) = eval_poly \<alpha> p + eval_poly \<alpha> q"
proof (induct p arbitrary: q, simp)
  case (Cons mc p)
  obtain m c where mc: "mc = (m,c)" by (cases mc, auto)
  show ?case
  proof (cases "extract (\<lambda> mc. fst mc =m m) q")
    case None
    show ?thesis by (simp add: Cons[of q] mc None field_simps)
  next
    case (Some res)
    obtain q1 md q2 where res: "res = (q1,md,q2)" by (cases res, auto)
    from extract_Some[OF Some[simplified res]] res obtain m' d where q: "q = q1 @ (m',d) # q2" and m': "m' =m m" and res: "res = (q1,(m',d),q2)" by (cases md, auto)
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
qed

declare poly_add.simps[simp del]

fun monom_mult_poly :: "('v monom \<times> 'a) \<Rightarrow> ('v,'a :: semiring_0)poly \<Rightarrow> ('v,'a)poly"
where "monom_mult_poly _ [] = []"
    | "monom_mult_poly (m,c) ((m',d) # p) = (if c * d = 0 then monom_mult_poly (m,c) p else (monom_mult m m', c * d) # monom_mult_poly (m,c) p)"

lemma monom_mult_poly_inv: assumes m: "monom_inv m" shows "poly_inv p \<Longrightarrow> poly_inv (monom_mult_poly (m,c) p)"
proof (induct p, simp add: poly_inv_def)
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
  proof (simp add: Pair, induct p, simp)
    case (Cons nd q)
    obtain n d where nd: "nd = (n,d)" by (cases nd, auto)
    show ?case
    proof (cases "c * d = 0")
      case False
      thus ?thesis by (simp add: nd Cons, simp only: field_simps)
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
  qed
qed

declare monom_mult_poly.simps[simp del]

fun poly_mult :: "('v,'a :: semiring_0)poly \<Rightarrow> ('v,'a)poly \<Rightarrow> ('v,'a)poly" 
where "poly_mult [] q = []"
   |  "poly_mult (mc # p) q = poly_add (monom_mult_poly mc q) (poly_mult p q)"

lemma poly_mult_inv: assumes p: "poly_inv p" and q: "poly_inv q"
  shows "poly_inv (poly_mult p q)"
using p
proof (induct p, simp add: poly_inv_def)
  case (Cons mc p)
  obtain m c where mc: "mc = (m,c)" by (cases mc, auto)
  with Cons(2) have m: "monom_inv m" and p: "poly_inv p" unfolding poly_inv_def by auto
  show ?case
    by (simp add: mc, rule poly_add_inv[OF monom_mult_poly_inv[OF m q] Cons(1)[OF p]])
qed

lemma poly_mult[simp]: "eval_poly \<alpha> (poly_mult p q) = eval_poly \<alpha> p * eval_poly \<alpha> q"
proof (induct p, simp)
  case (Cons mc p)
  thus ?case
    by (simp add: field_simps)
qed

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
by (induct p, (simp add: zero_poly_def one_poly_def)+)

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
proof (induct m, simp add: one_poly_inv)
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
proof (induct p, simp add: zero_poly_inv)
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
      assumes eq: "\<And> w. eval_poly \<alpha> (f w) = eval_poly (\<lambda> w. eval_poly \<alpha> (g w)) (q w)"
      shows "eval_poly (\<lambda> w. eval_poly \<alpha> (f w)) p = eval_poly (\<lambda> w. eval_poly \<alpha> (g w)) (poly_subst q p)" 
proof (induct p, simp add: poly_subst.simps zero_poly_def)
  case (Cons mc p)
  obtain m c where mc: "mc = (m,c)" by (cases mc, auto)
  have id: "eval_monom (\<lambda>w. eval_poly \<alpha> (f w)) m =  eval_monom (\<lambda>v. eval_poly (\<lambda>w. eval_poly \<alpha> (g w)) (q v)) m"
  proof (induct m, simp)
    case (Cons wp m)
    obtain w p where wp: "wp = (w,p)" by (cases wp, auto)
    show ?case
      by (simp add: wp Cons eq)
  qed
  show ?case
    by (simp add: mc Cons poly_subst.simps id, simp add: field_simps)
qed

(* the list of variables occuring in p *)
definition poly_vars_list :: "('v,'a)poly \<Rightarrow> 'v list"
where "poly_vars_list p = remdups (List.maps (map fst o fst) p)"

(* check whether a variable occurs in p *)
definition poly_var :: "('v,'a)poly \<Rightarrow> 'v \<Rightarrow> bool"
where "poly_var p v = (v : set(List.maps (map fst o fst) p))"

lemma poly_vars_list: assumes eq: "\<And> w. w \<in> set (poly_vars_list p) \<Longrightarrow> f w = g w"
  shows "poly_subst f p = poly_subst g p" 
using eq
proof (induct p, simp)
  case (Cons mc p)
  hence rec: "poly_subst f p = poly_subst g p" by(auto simp: poly_vars_list_def maps_def)
  show ?case
  proof (cases mc)
    case (Pair m c)
    with Cons(2) have "\<And> w. w \<in> set (map fst m) \<Longrightarrow> f w = g w" by(auto simp: poly_vars_list_def maps_def)
    hence "monom_subst f m = monom_subst g m"
    proof (induct m, simp add: monom_subst.simps)
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
qed

lemma poly_var: assumes pv: "\<not> poly_var p v" and diff: "\<And> w. v \<noteq> w \<Longrightarrow> f w = g w"
  shows "poly_subst f p = poly_subst g p"
proof (rule poly_vars_list)
  fix w
  assume "w \<in> set (poly_vars_list p)"
  thus "f w = g w" using pv diff unfolding poly_vars_list_def poly_var_def maps_def by (cases "v = w", auto)
qed

           
declare poly_subst.simps[simp del]



subsection {*
  Polynomial orders
*}

definition pos_assign :: "('v,'a :: ordered_semiring_0)assign \<Rightarrow> bool"
where "pos_assign \<alpha> = (\<forall> x. \<alpha> x \<ge> 0)"

definition poly_ge :: "('v,'a :: poly_carrier)poly \<Rightarrow> ('v,'a)poly \<Rightarrow> bool" (infix "\<ge>p" 51)
where "p \<ge>p q = (\<forall> \<alpha>. pos_assign \<alpha> \<longrightarrow> ge (eval_poly \<alpha> p) (eval_poly \<alpha> q))"

lemma poly_ge_refl[simp]: "p \<ge>p p"
unfolding poly_ge_def using ge_refl by auto

lemma poly_ge_trans[trans]: "\<lbrakk>p1 \<ge>p p2; p2 \<ge>p p3\<rbrakk> \<Longrightarrow> p1 \<ge>p p3"
using assms unfolding poly_ge_def using ge_trans by blast


lemma pos_assign_monom: fixes \<alpha> :: "('v,'a :: poly_carrier)assign"
  assumes pos: "pos_assign \<alpha>"
  shows "ge (eval_monom \<alpha> m) 0"
proof (induct m, simp add: one_ge_zero)
  case (Cons xp m)
  show ?case
  proof (cases xp)
    case (Pair x p)
    from pos[unfolded pos_assign_def] have ge: "ge (\<alpha> x) 0" by simp
    have ge: "ge (\<alpha> x ^ p) 0"
    proof (induct p, simp add: one_ge_zero)
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
  shows "ge (eval_poly \<alpha> p) 0"
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
where "p >p q = (\<forall> \<alpha>. pos_assign \<alpha> \<longrightarrow> gt (eval_poly \<alpha> p) (eval_poly \<alpha> q))"

lemma poly_gt_imp_poly_ge: "p >p q \<Longrightarrow> p \<ge>p q" unfolding poly_ge_def poly_gt_def using gt_imp_ge by blast

abbreviation poly_GT :: "('v,'a)poly ars"
where "poly_GT \<equiv> {(p,q) | p q. p >p q \<and> q \<ge>p zero_poly}"

lemma poly_compat: "\<lbrakk>p1 \<ge>p p2; p2 >p p3\<rbrakk> \<Longrightarrow> p1 >p p3"
using assms unfolding poly_ge_def poly_gt_def using compat by blast

lemma poly_compat2: "\<lbrakk>p1 >p p2; p2 \<ge>p p3\<rbrakk> \<Longrightarrow> p1 >p p3"
using assms unfolding poly_ge_def poly_gt_def using compat2 by blast

lemma poly_GT_SN: "SN poly_GT"
proof
  fix f
  assume f: "\<forall> i. (f i, f (Suc i)) \<in> poly_GT"
  have pos: "pos_assign ((\<lambda> x. 0) :: ('v,'a)assign)" (is "pos_assign ?ass") unfolding pos_assign_def using ge_refl by auto
  obtain g where g: "\<And> i. g i = eval_poly ?ass (f i)" by auto
  from f pos have "\<forall> i. ge (g (Suc i)) 0 \<and> gt (g i) (g (Suc i))" unfolding poly_gt_def g using pos_assign_poly by auto
  with SN show False unfolding SN_defs by blast 
qed
end

text {* monotonicity of polynomials *}

definition poly_weak_mono_all :: "'w \<Rightarrow> ('v,'a :: poly_carrier)poly \<Rightarrow> bool"
where "poly_weak_mono_all type p \<equiv> \<forall> (f :: 'v \<Rightarrow> ('w,'a)poly) g. (\<forall> x. f x \<ge>p g x \<and> g x \<ge>p zero_poly) \<longrightarrow> poly_subst f p \<ge>p poly_subst g p"
      
      
definition poly_weak_mono :: "'w \<Rightarrow> ('v,'a :: poly_carrier)poly \<Rightarrow> 'v \<Rightarrow> bool"
where "poly_weak_mono type p v \<equiv> \<forall> f g :: ('v \<Rightarrow> ('w,'a)poly). (\<forall> w. (v \<noteq> w \<longrightarrow> f w = g w) \<and> g w \<ge>p zero_poly) \<and> (f v \<ge>p g v) \<longrightarrow> poly_subst f p \<ge>p poly_subst g p"

lemma poly_weak_mono: fixes type :: 'w and p :: "('v,'a :: poly_carrier)poly"
  assumes "\<And> v. v \<in> set (poly_vars_list p) \<Longrightarrow> poly_weak_mono type p v"
  shows "poly_weak_mono_all type p"
unfolding poly_weak_mono_all_def
proof (intro allI impI)
  fix f g :: "'v \<Rightarrow> ('w,'a)poly"
  assume "\<forall> v. f v \<ge>p g v \<and> g v \<ge>p zero_poly"
  hence ge: "\<And> v . f v \<ge>p g v" and gz: "\<And> v. g v \<ge>p zero_poly" by auto
  let ?fg = "\<lambda> vs v. if (v \<in> set vs) then f v else g v"
  {
    fix vs :: "'v list"
    assume "set vs \<subseteq> set (poly_vars_list p)"
    hence "poly_subst (?fg vs) p \<ge>p poly_subst g p"
    proof (induct vs, simp)
      case (Cons v vs)
      hence subset: "set vs \<subseteq> set (poly_vars_list p)"  and v: "v \<in> set (poly_vars_list p)" by auto
      show ?case
        by (rule poly_ge_trans[OF _ Cons(1)[OF subset]], rule assms[OF v, unfolded poly_weak_mono_def, THEN spec, THEN spec, THEN mp], simp add: ge gz poly_ge_trans[OF ge gz])
    qed
  }
  hence one: "poly_subst (?fg (poly_vars_list p)) p \<ge>p poly_subst g p" by simp
  have two: "poly_subst (?fg (poly_vars_list p)) p = poly_subst f p" 
    by (rule poly_vars_list, auto)
  show "poly_subst f p \<ge>p poly_subst g p" using one two by auto
qed
  

lemma poly_weak_mono_all: fixes p :: "('v,'a :: poly_carrier)poly" and type :: 'w
  assumes "poly_weak_mono_all type p"
  shows "poly_weak_mono type p v"
unfolding poly_weak_mono_def
proof (intro allI impI)
  fix f g :: "'v \<Rightarrow> ('w,'a)poly"
  assume ass: " (\<forall>w. (v \<noteq> w \<longrightarrow> f w = g w) \<and> g w \<ge>p zero_poly) \<and> f v \<ge>p g v"
  show "poly_subst f p \<ge>p poly_subst g p"
  proof (rule assms[unfolded poly_weak_mono_all_def, THEN spec, THEN spec, THEN mp], intro allI)
    fix w
    show "f w \<ge>p g w \<and> g w \<ge>p zero_poly"
      using ass ge_refl by (cases "v = w", auto)
  qed
qed

lemma poly_weak_mono_all_pos: 
  fixes type :: 'v and p :: "('v,'a :: poly_carrier)poly"
  assumes pos_at_zero: "ge (eval_poly (\<lambda> w. 0) p) 0"
  and mono: "poly_weak_mono_all type p"
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
      by (rule mono[unfolded poly_weak_mono_all_def, THEN spec[of _ ?id], THEN spec[of _ ?z], THEN mp], 
        simp add: poly_ge_refl, simp add: poly_ge_def zero_poly_def pos_assign_def) 
    hence "ge (eval_poly \<alpha> (poly_subst ?id p)) (eval_poly \<alpha> (poly_subst ?z p))" unfolding poly_ge_def using pos by simp
    also have "\<dots> = eval_poly (\<lambda> w. 0) p" by (simp add: poly_subst zero_poly_def)
    also have "ge \<dots> 0" by (rule pos_at_zero)
    finally show ?thesis by  (simp add: poly_subst)
  qed
qed

lemma monom_subst_mono: fixes \<alpha> :: "('v,'a :: poly_carrier)assign"
  assumes pos: "pos_assign \<alpha>"
  and fg: "\<And> v. f v \<ge>p g v"
  and g: "\<And> v. g v \<ge>p zero_poly"
  shows "ge (eval_poly \<alpha> (monom_subst f m)) (eval_poly \<alpha> (monom_subst g m))" 
proof -
  let ?f = "\<lambda> v. eval_poly \<alpha> (f v)"
  let ?g = "\<lambda> v. eval_poly \<alpha> (g v)"
  have fg: "\<And> v. ?f v \<ge> ?g v" and g: "\<And> v. ?g v \<ge> 0"  using fg g pos unfolding poly_ge_def zero_poly_def by auto
  have "(eval_monom ?f m \<ge> eval_monom ?g m) \<and> (eval_monom ?g m \<ge> 0)" 
  proof (induct m, simp add: ge_refl one_ge_zero)
    case (Cons vn m)
    show ?case 
    proof (cases vn)
      case (Pair v n)
      from Cons have one: "eval_monom ?f m \<ge> eval_monom ?g m" and one': "eval_monom ?g m \<ge> 0" by simp+
      { (* perhaps extract this proof *)
        fix a b :: 'a and n :: nat
        assume ge: "ge a b" and ze: "ge b 0"
        have "ge (a^n) (b^n) \<and> ge (b^n) 0"
        proof (induct n, simp add: ge_refl one_ge_zero)
          case (Suc n)
          hence rec1: "a ^ n \<ge> b ^ n" and rec2: "b ^ n \<ge> 0" by auto
          from times_left_mono[OF ze rec2] have one: "b ^ Suc n \<ge> 0" by (auto simp: field_simps)
          have "a * a ^n \<ge> a * b ^ n" using times_left_mono[OF ge_trans[OF ge ze] rec1] by (simp add: field_simps)
          also have "\<dots> \<ge> b * b ^ n" using times_left_mono[OF rec2 ge] .
          finally  show ?case by (simp only: one, simp)
        qed
      } note power_mono = this
      from power_mono[OF fg g]
      have two: "?f v^n \<ge> ?g v^n" and two': "?g v^n \<ge> 0" by auto
      from times_left_mono[OF ge_trans[OF one one'] two] have "eval_monom ?f m * ?f v^n \<ge> eval_monom ?f m * ?g v^n" by (auto simp: field_simps)
      also have "\<dots> \<ge> eval_monom ?g m * ?g v^n" using times_left_mono[OF two' one] .
      finally have res1: "eval_monom ?f m * ?f v^n \<ge> eval_monom ?g m * ?g v^n" .
      from times_left_mono[OF two' one'] have res2: "eval_monom ?g m * ?g v^n \<ge> 0" by simp
      show ?thesis by (simp add: Pair res1 res2)
    qed
  qed
  thus ?thesis by simp
qed    

context poly_order_carrier
begin

definition poly_strict_mono :: "'w \<Rightarrow> ('v,'a)poly \<Rightarrow> 'v \<Rightarrow> bool"
  where "poly_strict_mono type p v \<equiv> \<forall> f g :: ('v \<Rightarrow> ('w,'a)poly). (\<forall> w. (v \<noteq> w \<longrightarrow> f w = g w) \<and> g w \<ge>p zero_poly) \<and> (f v >p g v) \<longrightarrow> poly_subst f p >p poly_subst g p"

lemma poly_add_gt_mono: assumes "p1 >p p2" shows "poly_add p1 q >p poly_add p2 q"
using assms unfolding poly_gt_def by (auto simp: field_simps plus_gt_left_mono)

lemma poly_mult_gt_mono: 
  fixes q :: "('v,'a)poly"
  assumes gt: "p1 >p p2" and mono: "q \<ge>p one_poly"
  shows "poly_mult p1 q >p poly_mult p2 q"
proof (unfold poly_gt_def, intro impI allI, simp)
  fix \<alpha> :: "('v,'a)assign"
  assume p: "pos_assign \<alpha>"
  with gt have gt: "gt (eval_poly \<alpha> p1) (eval_poly \<alpha> p2)" unfolding poly_gt_def by simp
  from mono p have one: "eval_poly \<alpha> q \<ge> 1" unfolding poly_ge_def one_poly_def by auto
  show "gt (eval_poly \<alpha> p1 * eval_poly \<alpha> q) (eval_poly \<alpha> p2 * eval_poly \<alpha> q)"
    using times_gt_mono[OF gt one] .
qed
end


subsection {* Executable and sufficient criteria to compare polynomials and ensure monotonicity *} 

text {* poly\_split extracts the coefficient for a given monomial and returns additionally the remaining polynomial *}
definition poly_split :: "('v monom) \<Rightarrow> ('v,'a :: zero)poly \<Rightarrow> 'a \<times> ('v,'a)poly" 
  where "poly_split m p \<equiv> case extract (\<lambda> (n,_). m =m n) p of None \<Rightarrow> (0,p) | Some (p1,(_,c),p2) \<Rightarrow> (c, p1 @ p2)"

lemma poly_split: assumes "poly_split m p = (c,q)"
  shows "p =p (m,c) # q"
proof (cases "extract (\<lambda> (n,_). m =m n) p")
  case None
  with assms have "(c,q) = (0,p)" unfolding poly_split_def by auto
  thus ?thesis unfolding eq_poly_def by auto
next
  case (Some res)
  obtain p1 mc p2 where "res = (p1,mc,p2)" by (cases res, auto)
  with extract_Some[OF Some[simplified this]] obtain a m' where p: "p = p1 @ (m',a) # p2" and m': "m =m m'" and res: "res = (p1,(m',a),p2)" by (cases mc, auto)
  from Some res assms have c: "c = a" and q: "q = p1 @ p2" unfolding poly_split_def by auto
  show ?thesis unfolding eq_poly_def by (simp add: p c q eq_monom[OF m'] field_simps)
qed 

lemma poly_split_eval: assumes "poly_split m p = (c,q)" 
  shows "eval_poly \<alpha> p = (eval_monom \<alpha> m * c) + eval_poly \<alpha> q"
using poly_split[OF assms] unfolding eq_poly_def by auto



fun check_poly_ge :: "('v,'a :: ordered_semiring_0)poly \<Rightarrow> ('v,'a)poly \<Rightarrow> bool"
where "check_poly_ge [] q = list_all (\<lambda> (_,d). ge 0 d) q"
    | "check_poly_ge ((m,c) # p) q = (case extract (\<lambda> nd. fst nd =m m) q of
                                         None \<Rightarrow> ge c 0 \<and> check_poly_ge p q
                                       | Some (q1,(_,d),q2) \<Rightarrow> ge c d \<and> check_poly_ge p (q1 @ q2))"

lemma check_poly_ge: fixes p :: "('v,'a :: poly_carrier)poly"
  shows "check_poly_ge p q \<Longrightarrow> p \<ge>p q"
proof (induct p arbitrary: q)
  case Nil
  hence "\<forall> (n,d) \<in> set q. ge 0 d" using list_all_iff[of _ q] by auto
  hence "[] \<ge>p q" 
  proof (induct q, simp add: poly_ge_refl)
    case (Cons nd q)
    hence rec: "[] \<ge>p q" by simp
    show ?case
    proof (cases nd)
      case (Pair n d)
      with Cons have ge: "ge 0 d" by auto
      show ?thesis 
      proof (simp add: Pair, unfold poly_ge_def, intro allI impI, simp)
        fix \<alpha> :: "('v,'a)assign"
        assume pos: "pos_assign \<alpha>"
        have ge: "ge 0 (eval_monom \<alpha> n * d)"
          using times_right_mono[OF pos_assign_monom[OF pos, of n] ge] by simp
        from rec[unfolded poly_ge_def] pos have ge2: "ge 0 (eval_poly \<alpha> q)" by auto
        show "ge 0 (eval_monom \<alpha> n * d + eval_poly \<alpha> q)" using ge_trans[OF plus_left_mono[OF ge] plus_right_mono[OF ge2]]
          by simp
      qed
    qed
  qed
  thus ?case by simp
next
  case (Cons mc p)
  obtain m c where mc: "mc = (m,c)" by (cases mc, auto)
  show ?case
  proof (cases "extract (\<lambda> mc. fst mc =m m) q")
    case None
    with Cons(2) have rec: "check_poly_ge p q" and c: "ge c 0" using mc by auto
    from Cons(1)[OF rec] have rec: "p \<ge>p q" .
    show ?thesis 
    proof (simp add: mc, unfold poly_ge_def, intro allI impI, simp)
      fix \<alpha> :: "('v,'a)assign"
      assume pos: "pos_assign \<alpha>"
      have ge: "ge (eval_monom \<alpha> m * c) 0"
        using times_right_mono[OF pos_assign_monom[OF pos, of m] c] by simp
      from rec have pq: "eval_poly \<alpha> p \<ge> eval_poly \<alpha> q" unfolding poly_ge_def using pos by auto
      show "eval_monom \<alpha> m * c + eval_poly \<alpha> p \<ge> eval_poly \<alpha> q"
        using ge_trans[OF plus_left_mono[OF ge] plus_right_mono[OF pq]] by simp
    qed
  next
    case (Some res)
    obtain q1 md q2 where "res = (q1,md,q2)" by (cases res, auto)
    with extract_Some[OF Some[simplified this]] obtain m' d where q: "q = q1 @ (m',d) # q2" and m': "m' =m m" and res: "res = (q1,(m',d),q2)" 
      by (cases md, auto)
    from Cons(2) Some mc res have rec: "check_poly_ge p (q1 @ q2)" and c: "ge c d" by auto
    from Cons(1)[OF rec] have p: "p \<ge>p q1 @ q2" .
    show ?thesis
    proof (simp add: mc, unfold poly_ge_def, intro allI impI)
      fix \<alpha> :: "('v,'a)assign"
      assume pos: "pos_assign \<alpha>"
      have ge: "ge (eval_monom \<alpha> m * c) (eval_monom \<alpha> m' * d)"
        using times_right_mono[OF pos_assign_monom[OF pos, of m] c] 
          eq_monom[OF m', of \<alpha>] by simp
      from p have ge2: "ge (eval_poly \<alpha> p) (eval_poly \<alpha> (q1 @ q2))" unfolding poly_ge_def using pos by auto
      show "ge (eval_poly \<alpha> ((m,c) # p)) (eval_poly \<alpha> q)" using ge_trans[OF plus_left_mono[OF ge] plus_right_mono[OF ge2]]
        by (simp add: q field_simps)
    qed
  qed
qed

declare check_poly_ge.simps[simp del]

definition check_poly_weak_mono_all :: "('v,'a :: ordered_semiring_0)poly \<Rightarrow> bool"
where "check_poly_weak_mono_all p \<equiv> list_all (\<lambda> (m,c). ge c 0) p"


lemma check_poly_weak_mono_all: fixes p :: "('v,'a :: poly_carrier)poly" and type :: 'w
  assumes "check_poly_weak_mono_all p" shows  "poly_weak_mono_all type p"
unfolding poly_weak_mono_all_def
proof (intro allI impI)
  fix f g :: "'v \<Rightarrow> ('w,'a)poly"
  assume fg: "\<forall> x. f x \<ge>p g x \<and> g x \<ge>p zero_poly"
  show "poly_subst f p \<ge>p poly_subst g p"
    unfolding poly_ge_def
  proof (intro allI impI)
    fix \<alpha> :: "('w,'a)assign"
    assume pos: "pos_assign \<alpha>"
    show "eval_poly \<alpha> (poly_subst f p) \<ge> eval_poly \<alpha> (poly_subst g p)"
    proof (simp only: poly_subst)
      let ?f = "\<lambda> v. eval_poly \<alpha> (f v)"
      let ?g = "\<lambda> v. eval_poly \<alpha> (g v)"
      have fg: "\<And> v. f v \<ge>p g v" and g: "\<And> v. g v \<ge>p  zero_poly"  using fg  by auto
      from assms have "\<And> m c. (m,c) \<in> set p \<Longrightarrow> ge c 0" unfolding check_poly_weak_mono_all_def by (auto simp: list_all_iff)
      thus "eval_poly ?f p \<ge> eval_poly ?g p"
      proof (induct p, simp add: ge_refl)
        case (Cons mc p)
        show ?case 
        proof (cases mc)
          case (Pair m c)
          with Cons have c: "c \<ge> 0" by auto
          from monom_subst_mono[OF pos fg g]
          have "(eval_monom ?f m \<ge> eval_monom ?g m)"  by force
          from times_left_mono[OF c this] have one: "eval_monom ?f m * c \<ge> eval_monom ?g m * c" .
          from Cons have two: "eval_poly ?f p \<ge> eval_poly ?g p" by auto
          from plus_left_mono[OF two] have "\<And> z. z + eval_poly ?f p \<ge> z + eval_poly ?g p" by (auto simp: field_simps)
          from ge_trans[OF plus_left_mono[OF one] this]
          show ?thesis by (simp add: Pair) 
        qed
      qed
    qed
  qed
qed

lemma check_poly_weak_mono_all_pos: 
  assumes "check_poly_weak_mono_all p" shows  "p \<ge>p zero_poly"
unfolding zero_poly_def
proof (rule check_poly_ge)
  from assms have "\<And> m c. (m,c) \<in> set p \<Longrightarrow> ge c 0" unfolding check_poly_weak_mono_all_def by (auto simp: list_all_iff)
  thus "check_poly_ge p []"
    by (induct p, simp add: check_poly_ge.simps,  clarify, auto simp: check_poly_ge.simps)
qed


text {* better check for weak monotonicity for discrete carriers: 
   $p$ is monotone in $v$ if $p(\ldots v+1 \ldots) \geq p(\ldots v \ldots)$ *}
definition check_poly_weak_mono_discrete :: "('v,'a :: poly_carrier)poly \<Rightarrow> 'v \<Rightarrow> bool"
  where "check_poly_weak_mono_discrete p v \<equiv> check_poly_ge (poly_subst (\<lambda> w. poly_of (if w = v then PSum [PNum 1, PVar v] else PVar w)) p) p"

definition check_poly_weak_mono_and_pos :: "bool \<Rightarrow> ('v,'a :: poly_carrier)poly \<Rightarrow> bool"
  where "check_poly_weak_mono_and_pos discrete p \<equiv> 
            if discrete then list_all (\<lambda> v. check_poly_weak_mono_discrete p v) (poly_vars_list p) \<and> ge (eval_poly (\<lambda> w. 0) p)  0
                        else check_poly_weak_mono_all p"

context poly_order_carrier
begin

lemma check_poly_weak_mono_discrete: 
  fixes v :: 'v and type :: 'w and p :: "('v,'a)poly"
  assumes discrete and check: "check_poly_weak_mono_discrete p v"
  shows "poly_weak_mono type p v"
unfolding poly_weak_mono_def 
proof (intro allI impI)
  fix f g :: "'v \<Rightarrow> ('w,'a)poly"
  assume ass: "(\<forall> w. (v \<noteq> w \<longrightarrow> f w = g w) \<and> g w \<ge>p zero_poly) \<and> f v \<ge>p g v"
  from assms check_poly_ge have ge: "poly_ge (poly_subst (\<lambda> w. poly_of (if w = v then PSum [PNum 1, PVar v] else PVar w)) p) p" (is "poly_ge ?p1 p") unfolding check_poly_weak_mono_discrete_def by blast
  show "poly_ge (poly_subst f p) (poly_subst g p)"
    unfolding poly_ge_def
  proof (intro allI impI, simp add: poly_subst)
    fix \<alpha> :: "('w,'a)assign"
    let ?fass = "\<lambda> w. eval_poly \<alpha> (f w)"
    let ?gass = "\<lambda> w. eval_poly \<alpha> (g w)"
    from ass have w: "\<And> w. v \<noteq> w \<Longrightarrow> f w = g w" by simp
    assume "pos_assign \<alpha>"
    with ass have v: "ge (eval_poly \<alpha> (f v)) (eval_poly \<alpha> (g v))" and gass: "pos_assign ?gass" unfolding poly_ge_def zero_poly_def pos_assign_def by auto
    from discrete[OF `discrete` v] obtain k' where id: "eval_poly \<alpha> (f v) = ((op + 1)^^k')  (eval_poly \<alpha> (g v))" by auto
    show "ge (eval_poly ?fass p) (eval_poly ?gass p)"
    proof (cases k')
      case 0
      have "(eval_poly ?fass p) = (eval_poly ?gass p)"
      proof (rule arg_cong[where f = "\<lambda> x. eval_poly x p"], intro ext)
        fix w
        from w id[simplified 0]
        show "eval_poly \<alpha> (f w) = eval_poly \<alpha> (g w)"
          by (cases "w = v", auto)
      qed
      thus ?thesis using ge_refl by simp
    next
      case (Suc k)
      with id have "eval_poly \<alpha> (f v) = ((op + 1)^^(Suc k))  (eval_poly \<alpha> (g v))" by simp 
      with w gass show "ge (eval_poly ?fass p) (eval_poly ?gass p)"
      proof (induct k arbitrary: f g rule: less_induct)
        case (less k)
        show ?case 
        proof (cases k)
          case 0
          with less have id0: "eval_poly \<alpha> (f v) = 1 + eval_poly \<alpha> (g v)" by simp
          have id1: "eval_poly (\<lambda> w. eval_poly \<alpha> (f w)) p = eval_poly (\<lambda> w. eval_poly \<alpha> (g w)) ?p1"
          proof (rule eval_poly_subst)
            fix w
            show "eval_poly \<alpha> (f w) = eval_poly (\<lambda> w. eval_poly \<alpha> (g w)) (poly_of (if w = v then PSum [PNum 1, PVar v] else PVar w))"
            proof (cases "w = v")
              case True
              show ?thesis by (simp add: True id0 zero_poly_def)
            next
              case False
              with less have "f w = g w" by simp
              thus ?thesis by (simp add: False)
            qed
          qed
          have "ge (eval_poly (\<lambda> w. eval_poly \<alpha> (g w)) ?p1) (eval_poly (\<lambda> w. eval_poly \<alpha> (g w)) p)" using ge less unfolding poly_ge_def by simp
          with id1 show ?thesis by simp
        next
          case (Suc kk)
          obtain g' where g': "g' = (\<lambda> w. if (w = v) then poly_add (poly_of (PNum 1)) (g w) else g w)" by auto
          {
            fix w
            have "eval_poly \<alpha> (g' w) = (if v = w then 1 else 0) + eval_poly \<alpha> (g w)"
              by (simp only: g', cases "v=w", auto)
          } note g'eval = this
          let ?g'ass = "\<lambda> w. eval_poly \<alpha> (g' w)"
          from less(3) have g'pos: "pos_assign ?g'ass" unfolding pos_assign_def 
          proof (simp add: g'eval)
            have "(1 :: 'a) + eval_poly \<alpha> (g v) \<ge> 1 + 0" 
              by (rule plus_right_mono, simp add: less(3)[unfolded pos_assign_def])
            also have "\<dots> = 1" by simp
            also have "\<dots> \<ge> 0" by (rule one_ge_zero)
            finally show "(1::'a) + eval_poly \<alpha> (g v) \<ge> 0" .
          qed
          {
            fix w
            assume "v \<noteq> w"
            hence "f w = g' w"
              unfolding g' by (simp add: less)
          } note w = this
          have eq: "eval_poly \<alpha> (f v) = (op + (1 :: 'a) ^^ Suc kk) (eval_poly \<alpha> (g' v))"
            by (simp add: less(4) g'eval Suc, rule arg_cong[where f = "op + 1"], induct kk, auto)
          from Suc have kk: "kk < k" by simp
          from less(1)[OF kk w g'pos] eq
          have rec1: "ge (eval_poly (\<lambda> w. eval_poly \<alpha> (f w)) p) (eval_poly (\<lambda> w. eval_poly \<alpha> (g' w)) p)" by simp
          { 
            fix w
            assume "v \<noteq> w"
            hence "g' w = g w"
              unfolding g' by simp
          } note w = this
          from Suc have z: "0 < k" by simp
          from less(1)[OF z w less(3)] g'
          have rec2: "ge (eval_poly (\<lambda> w. eval_poly \<alpha> (g' w)) p) (eval_poly (\<lambda> w. eval_poly \<alpha> (g w)) p)" by simp
          show ?thesis by (rule ge_trans[OF rec1 rec2])
        qed
      qed
    qed
  qed
qed

lemma check_poly_weak_mono_and_pos: 
  fixes p :: "('v,'a)poly" and type :: 'w
  assumes "check_poly_weak_mono_and_pos discrete p"
  shows "poly_weak_mono_all type p \<and> (p \<ge>p zero_poly)"
proof (cases discrete)
  case False
  with assms have c: "check_poly_weak_mono_all p" unfolding check_poly_weak_mono_and_pos_def
    by auto
  from check_poly_weak_mono_all[OF c] check_poly_weak_mono_all_pos[OF c] show ?thesis by auto
next
  case True
  with assms have c: "list_all (\<lambda> v. check_poly_weak_mono_discrete p v) (poly_vars_list p)" and g: "ge (eval_poly (\<lambda> w. 0) p) 0"
    unfolding check_poly_weak_mono_and_pos_def by auto
  have m: "poly_weak_mono_all type p"
  proof (rule poly_weak_mono)
    fix v :: 'v
    assume v: "v \<in> set (poly_vars_list p)"
    show "poly_weak_mono type p v"
      by (rule check_poly_weak_mono_discrete[OF True], rule c[unfolded list_all_iff, THEN bspec[OF _ v]]) 
  qed
  obtain vtype where "(vtype :: 'v) = vtype" by simp
  have m': "poly_weak_mono_all vtype p"
  proof (rule poly_weak_mono)
    fix v :: 'v
    assume v: "v \<in> set (poly_vars_list p)"
    show "poly_weak_mono vtype p v"
      by (rule check_poly_weak_mono_discrete[OF True], rule c[unfolded list_all_iff, THEN bspec[OF _ v]]) 
  qed
  from poly_weak_mono_all_pos[OF g m'] m show ?thesis by auto
qed

end

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
  and gt: "gt (\<alpha> v) (\<beta> v)"
  and ge: "ge (\<beta> v) 0"
  shows "gt (eval_monom \<alpha> m) (eval_monom \<beta> m)"
proof (cases power_mono)
  case False
  with check have "m = [(v,1)]" unfolding check_monom_strict_mono_def by (cases m, cases "tl m", cases "hd m", auto)
  with gt show ?thesis by (auto)
next
  case True
  with check obtain n where m: "m = [(v,n)]" and n: "1 \<le> n" unfolding check_monom_strict_mono_def by (cases m, cases "tl m", cases "hd m", auto)
  from power_mono[OF True gt ge n] m show ?thesis by auto
qed

lemma check_poly_strict_mono: fixes type :: 'w
  assumes check1: "check_poly_strict_mono power_mono p v"
  and check2: "check_poly_weak_mono_all p"
  shows "poly_strict_mono type p v"
unfolding poly_strict_mono_def
proof (intro allI impI, clarify)
  fix f g :: "'b \<Rightarrow> ('w,'a)poly"
  assume fgw: "\<forall> w. (v \<noteq> w \<longrightarrow> f w = g w) \<and> g w \<ge>p zero_poly" and fgv: "f v >p g v"
  from fgw poly_gt_imp_poly_ge[OF fgv] have fgw2: "\<forall> w. f w \<ge>p g w \<and> g w \<ge>p zero_poly" using poly_ge_refl by force
  show "poly_subst f p >p poly_subst g p"
    unfolding poly_gt_def
  proof (intro allI impI)
    fix \<alpha> :: "('w,'a)assign"
    assume pos: "pos_assign \<alpha>"
    let ?e = "\<lambda> f p. eval_poly \<alpha> (poly_subst f p)"
    show "gt (?e f p) (?e g p)"
      using check1[unfolded check_poly_strict_mono_def, simplified list_ex_iff]
        check2[unfolded check_poly_weak_mono_all_def, simplified list_all_iff, THEN bspec]
    proof (induct p, simp)
      case (Cons mc p)
      obtain m c where mc: "mc = (m,c)" by (cases mc, auto)
      show ?case 
      proof (cases "(c \<ge> 1) \<and> check_monom_strict_mono power_mono m v")
        case True
        hence c: "c \<ge> 1" and m: "check_monom_strict_mono power_mono m v" by blast+
        have "gt (eval_poly \<alpha> (monom_subst f m)) (eval_poly \<alpha> (monom_subst g m))" (is "gt ?emf ?emg")
          by (simp add: monom_subst.simps one_poly_def, rule check_monom_strict_mono[OF m], 
              rule fgv[unfolded poly_gt_def, THEN spec, THEN mp[OF _ pos]], 
              rule fgw[unfolded poly_ge_def zero_poly_def, THEN spec, of v, simplified, THEN spec, THEN mp[OF _ pos]])
        from times_gt_mono[OF this c] have gt: "gt (c * ?emf) (c * ?emg)" by (auto simp: field_simps)
        from Cons(3) have "check_poly_weak_mono_all p" unfolding check_poly_weak_mono_all_def list_all_iff by auto
        from check_poly_weak_mono_all[OF this, unfolded poly_weak_mono_all_def, THEN spec, THEN spec, THEN mp[OF _ fgw2]]
        have ge: "poly_subst f p \<ge>p poly_subst g p" by auto
        show ?thesis by (simp add: mc poly_subst.simps del: monom_subst, rule compat2[OF plus_gt_left_mono[OF gt]],
          simp only: add_commute[of "c * ?emg" _], rule plus_left_mono, rule ge[unfolded poly_ge_def, THEN spec, THEN mp[OF _ pos]])
      next
        case False
        with Cons(2) mc have "\<exists> mc \<in> set p. (\<lambda> (m,c). (c \<ge> 1) \<and> check_monom_strict_mono power_mono m v) mc" by auto
        from Cons(1)[OF this] Cons(3) have rec: "gt (?e f p) (?e g p)" by simp
        from Cons(3) mc have c: "c \<ge> 0" by auto
        have "ge (eval_poly \<alpha> (monom_subst f m)) (eval_poly \<alpha> (monom_subst g m))" (is "ge ?emf ?emg")
          using monom_subst_mono[OF pos, of f g] fgw2 by blast
        from times_left_mono[OF c this] have ge: "c * ?emf \<ge> c * ?emg" by (auto simp: field_simps)
        show ?thesis by (simp add: mc poly_subst.simps del: monom_subst, simp only: field_simps, rule
           compat2[OF plus_gt_left_mono[OF rec] plus_left_mono[OF ge, simplified add_commute[of "c * ?emf"] add_commute[of "c * ?emg"]]])
      qed
    qed
  qed
qed     
      

lemma check_poly_gt: 
  fixes p :: "('v,'a)poly"
  assumes "check_poly_gt gt p q" shows "p >p q"
proof -
  obtain a1 p1 where p: "poly_split [] p = (a1,p1)" by (cases "poly_split [] p", auto)
  obtain b1 q1 where q: "poly_split [] q = (b1,q1)" by (cases "poly_split [] q", auto)
  from p q assms have gt: "gt a1 b1" and ge: "p1 \<ge>p q1" unfolding check_poly_gt_def using check_poly_ge[of p1 q1]  by auto
  show ?thesis
  proof (unfold poly_gt_def, intro impI allI)
    fix \<alpha> :: "('v,'a)assign"
    assume "pos_assign \<alpha>"
    with ge have ge: "ge (eval_poly \<alpha> p1) (eval_poly \<alpha> q1)" unfolding poly_ge_def by simp
    from plus_gt_left_mono[OF gt] compat[OF plus_left_mono[OF ge]] have gt: "gt (a1 + eval_poly \<alpha> p1) (b1 + eval_poly \<alpha> q1)" by (force simp: field_simps)
    show "gt (eval_poly \<alpha> p) (eval_poly \<alpha> q)"
      by (simp add: poly_split[OF p, unfolded eq_poly_def] poly_split[OF q, unfolded eq_poly_def] gt)
  qed
qed


lemma check_poly_strict_mono_discrete: 
  fixes v :: 'v and type :: 'w
  assumes discrete and check: "check_poly_strict_mono_discrete gt p v"
  shows "poly_strict_mono type p v"
unfolding poly_strict_mono_def 
proof (intro allI impI)
  fix f g :: "'v \<Rightarrow> ('w,'a)poly"
  assume ass: "(\<forall> w. (v \<noteq> w \<longrightarrow> f w = g w) \<and> g w \<ge>p zero_poly) \<and> poly_gt (f v) (g v)"
  from assms check_poly_gt have gt: "poly_gt (poly_subst (\<lambda> w. poly_of (if w = v then PSum [PNum 1, PVar v] else PVar w)) p) p" (is "poly_gt ?p1 p") unfolding check_poly_strict_mono_discrete_def by blast
  show "poly_gt (poly_subst f p) (poly_subst g p)"
    unfolding poly_gt_def
  proof (intro allI impI, simp add: poly_subst)
    fix \<alpha> :: "('w,'a)assign"
    let ?fass = "\<lambda> w. eval_poly \<alpha> (f w)"
    let ?gass = "\<lambda> w. eval_poly \<alpha> (g w)"
    from ass have w: "\<And> w. v \<noteq> w \<Longrightarrow> f w = g w" by simp
    assume "pos_assign \<alpha>"
    with ass have v: "gt (eval_poly \<alpha> (f v)) (eval_poly \<alpha> (g v))" and gass: "pos_assign ?gass" unfolding poly_gt_def poly_ge_def zero_poly_def pos_assign_def by auto
    have neq: "\<not> eval_poly \<alpha> (f v) = eval_poly \<alpha> (g v)"
    proof  
      assume "eval_poly \<alpha> (f v) = eval_poly \<alpha> (g v)"
      with v have "gt (eval_poly \<alpha> (g v)) (eval_poly \<alpha> (g v))" by simp
      with gass[unfolded pos_assign_def, THEN spec, of v] SN show False unfolding SN_defs by auto
    qed
    from discrete[OF `discrete` gt_imp_ge[OF v]] obtain k' where "eval_poly \<alpha> (f v) = ((op + 1)^^k')  (eval_poly \<alpha> (g v))" by auto
    then obtain k where "eval_poly \<alpha> (f v) = ((op + 1)^^(Suc k))  (eval_poly \<alpha> (g v))" 
      by (cases k', auto simp: neq)
    with w gass show "gt (eval_poly ?fass p) (eval_poly ?gass p)"
    proof (induct k arbitrary: f g rule: less_induct)
      case (less k)
      show ?case 
      proof (cases k)
        case 0
        with less have id0: "eval_poly \<alpha> (f v) = 1 + eval_poly \<alpha> (g v)" by simp
        have id1: "eval_poly (\<lambda> w. eval_poly \<alpha> (f w)) p = eval_poly (\<lambda> w. eval_poly \<alpha> (g w)) ?p1"
        proof (rule eval_poly_subst)
          fix w
          show "eval_poly \<alpha> (f w) = eval_poly (\<lambda> w. eval_poly \<alpha> (g w)) (poly_of (if w = v then PSum [PNum 1, PVar v] else PVar w))"
          proof (cases "w = v")
            case True
            show ?thesis by (simp add: True id0 zero_poly_def)
          next
            case False
            with less have "f w = g w" by simp
            thus ?thesis by (simp add: False)
          qed
        qed
        have "gt (eval_poly (\<lambda> w. eval_poly \<alpha> (g w)) ?p1) (eval_poly (\<lambda> w. eval_poly \<alpha> (g w)) p)" using gt less unfolding poly_gt_def by simp
        with id1 show ?thesis by simp
      next
        case (Suc kk)
        obtain g' where g': "g' = (\<lambda> w. if (w = v) then poly_add (poly_of (PNum 1)) (g w) else g w)" by auto
        {
          fix w
          have "eval_poly \<alpha> (g' w) = (if v = w then 1 else 0) + eval_poly \<alpha> (g w)"
            by (simp only: g', cases "v=w", auto)
        } note g'eval = this
        let ?g'ass = "\<lambda> w. eval_poly \<alpha> (g' w)"
        from less(3) have g'pos: "pos_assign ?g'ass" unfolding pos_assign_def 
        proof (simp add: g'eval)
          have "(1 :: 'a) + eval_poly \<alpha> (g v) \<ge> 1 + 0" 
            by (rule plus_right_mono, simp add: less(3)[unfolded pos_assign_def])
          also have "\<dots> = 1" by simp
          also have "\<dots> \<ge> 0" by (rule one_ge_zero)
          finally show "(1::'a) + eval_poly \<alpha> (g v) \<ge> 0" .
        qed
        {
          fix w
          assume "v \<noteq> w"
          hence "f w = g' w"
            unfolding g' by (simp add: less)
        } note w = this
        have eq: "eval_poly \<alpha> (f v) = (op + (1 :: 'a) ^^ Suc kk) (eval_poly \<alpha> (g' v))"
          by (simp add: less(4) g'eval Suc, rule arg_cong[where f = "op + 1"], induct kk, auto)
        from Suc have kk: "kk < k" by simp
        from less(1)[OF kk w g'pos] eq
        have rec1: "gt (eval_poly (\<lambda> w. eval_poly \<alpha> (f w)) p) (eval_poly (\<lambda> w. eval_poly \<alpha> (g' w)) p)" by simp
        { 
          fix w
          assume "v \<noteq> w"
          hence "g' w = g w"
            unfolding g' by simp
        } note w = this
        from Suc have z: "0 < k" by simp
        from less(1)[OF z w less(3)] g'
        have rec2: "gt (eval_poly (\<lambda> w. eval_poly \<alpha> (g' w)) p) (eval_poly (\<lambda> w. eval_poly \<alpha> (g w)) p)" by simp
        show ?thesis by (rule compat[OF gt_imp_ge[OF rec1] rec2])
      qed
    qed
  qed
qed

lemma check_poly_strict_mono_smart: fixes type :: 'w
  assumes check1: "check_poly_strict_mono_smart discrete power_mono gt p v"
  and check2: "check_poly_weak_mono_and_pos discrete p"
  shows "poly_strict_mono type p v"
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
