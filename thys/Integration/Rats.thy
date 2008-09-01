(* The rational numbers as subset of the real type. 

by Stefan Richter, TUM 2002.

This theory should really be subsumed by the construction of the
rational numbers as part of the development of the reals in
Real/Rational.thy. Any volunteers? (TN) *)

header {*The Rational Numbers*}

theory Rats
imports Complex_Main NatPair
begin

text{*A dense and countable subset of the @{text real} type was needed for
  some measurability proofs. That is why I developed this
  theory. Apparently, something similar exists in Isabelle2004 by now,
  but I have not checked it for applicability yet.

  To begin with, an injective function from $\mathbb{N}^2$ to
  $\mathbb{N}$ is defined\footnote{The function as well as the proofs
are derived from a german recursion theory textbook
  \cite[p.~85f]{Oberschelp1993}. Surjectivity is not needed here but
Larry Paulson suggested to prove it for completeness.}. Its inverse is
then a surjective
  mapping into $\mathbb{N}^2$. Another iteration yields three natural
  numbers, one for enumerator, denominator, and sign respectively. The
  rationals are now exactly the range of the resulting function on
  $\mathbb{N}$, which already proves 
  them countable, without even defining this concept. Much to my
delight, these functions could be reused for the simple
  function integral properties.*}
(*
definition
  n2_to_n:: "(nat * nat) \<Rightarrow> nat" where
  "n2_to_n pair = (let (n,m) = pair in (n+m) * Suc (n+m) div 2 + n)"

definition
  n_to_n2::  "nat \<Rightarrow> (nat * nat)" where
  "n_to_n2 = inv n2_to_n"
*)
definition
  n3_to_rat:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
  "n3_to_rat a b c = (if 2 dvd a then real b / real c else - real b /real c)"

definition
  nat_to_rat:: "nat \<Rightarrow> real" where
  "nat_to_rat n = (let (a,x) = nat_to_nat2 n ;  (b,c) = nat_to_nat2 x in
    n3_to_rat a b c)"

(* FIXME use the Rats provided already! *)
no_notation    Rats ("\<rat>")

definition
  Rats:: "real set" ("\<rat>") where
  "\<rat> = range nat_to_rat"

theorem nat_nat_rats: "real (a::nat)/real (b::nat) \<in> \<rat>"
proof -
  from nat_to_nat2_surj obtain x where "(a,b) = nat_to_nat2 x" 
    by (auto simp only: surj_def) 
  also from nat_to_nat2_surj obtain n where "(0,x) = nat_to_nat2 n" 
    by (auto simp only: surj_def)
  moreover have "n3_to_rat 0 a b = real a/real b" 
    by (simp add: n3_to_rat_def) 
  ultimately have "real a/real b = nat_to_rat n" 
    by (auto simp add: nat_to_rat_def Let_def split: split_split)
  hence "real a/real b \<in> range nat_to_rat" 
    by (auto simp add: image_def) 
  thus ?thesis 
    by (simp add: Rats_def)
qed

theorem minus_nat_nat_rats: "- real (a::nat)/real (b::nat) \<in> \<rat>"
proof -
  from nat_to_nat2_surj obtain x where "(a,b) = nat_to_nat2 x" 
    by (auto simp only: surj_def) 
  also from nat_to_nat2_surj obtain n where "(1,x) = nat_to_nat2 n" 
    by (auto simp only: surj_def)
  moreover have "n3_to_rat 1 a b = - real a/real b" 
    by (simp add: n3_to_rat_def) 
  ultimately have "- real a/real b = nat_to_rat n" 
    by (auto simp add: nat_to_rat_def Let_def split: split_split)
  hence "- real a/real b \<in> range nat_to_rat" 
    by (auto simp add: image_def) 
  thus ?thesis 
    by (simp add: Rats_def)
qed

text{*The following lemmata do not seem to exist in the @{text
  Real} theory,
  but I think they should. The proof is of unexpected complexity, since there are a
  number of theorems on @{text abs}, conversion from @{text int} to @{text real}, etc.~missing. *}(*<*)

theorem int_int_rats: "real (a::int)/real (b::int) \<in> \<rat>"
proof (cases "real a/real b < 0")
  case False
  hence "(real a/real b) = \<bar>real a/real b\<bar>" 
    by arith
  also have "\<dots> = real \<bar>a\<bar>/real \<bar>b\<bar>"
    by simp
  also have "\<dots> = real (nat \<bar>a\<bar>)/real (nat \<bar>b\<bar>)" by simp
  finally show ?thesis 
    by (simp only: nat_nat_rats)
next
  case True
  hence "(real a/real b) = -\<bar>real a/real b\<bar>" 
    by arith
  also have "\<dots> = - real (nat \<bar>a\<bar>)/real (nat \<bar>b\<bar>)" 
    by (simp add: real_of_int_abs)
  finally show ?thesis txt{*\nopagebreak*}
    by (simp only: minus_nat_nat_rats)
qed

theorem assumes a: "z \<in> \<rat>"
shows rats_int_int: "\<exists> x y. z = real (x::int)/real (y::int)"
(*<*)proof -
  from a obtain n where "z=nat_to_rat n" 
    by (auto simp only: Rats_def)
  also  have "\<dots> =  (let (a,x) = nat_to_nat2 n ;  (b,c) = nat_to_nat2 x in
  n3_to_rat a b c)" by (simp only: nat_to_rat_def)
  also have "\<dots> = n3_to_rat (fst (nat_to_nat2 n)) (fst (nat_to_nat2 (snd (nat_to_nat2 n)))) (snd (nat_to_nat2 (snd (nat_to_nat2 n))))"
    by (simp add: Let_def split: split_split)
  also obtain a b c where "\<dots> = n3_to_rat a b c" by blast
  also have "\<exists> x y. \<dots> = real (x::int)/real (y::int)"
  proof (cases "2 dvd a")
    case True 
    hence "n3_to_rat a b c = real (int b)/real (int c)"  by (simp add: n3_to_rat_def real_of_int_real_of_nat)
    thus ?thesis by fast
  next  
    case False
    hence "n3_to_rat a b c = real (-int b)/real (int c)" by (simp add: n3_to_rat_def real_of_int_real_of_nat)
    thus ?thesis by fast
  qed
  
  finally show ?thesis .
qed(*>*)


theorem assumes a: "z \<in> \<rat>"
shows rats_int_intnot0: "\<exists> x y. z = real (x::int)/real (y::int) \<and> y\<noteq>0"
(*<*)proof -
  from a have "\<exists> x y. z = real (x::int)/real (y::int)" by (rule rats_int_int)
  then obtain x y where xy: "z = real (x::int) / real (y::int)" by fast
  thus ?thesis  
  proof (cases "0=z")
    case False
    with xy have "y\<noteq>0"
      by simp
    with xy show ?thesis by fast
  next
    case True
    hence "z = real (0::int) / real (1::int) \<and> (1::int)\<noteq>(0::int)" by simp
    thus ?thesis by fast
  qed
qed(*>*)    


theorem assumes a: "a \<in> \<rat>" and b: "b \<in> \<rat>"
  shows rats_plus_rats: "a+b \<in> \<rat>"
proof -
  from a obtain x y where "a = real (x::int)/real (y::int) \<and> y\<noteq>0" 
    by (force simp add: rats_int_intnot0) 
  also from b obtain xb yb where "b = real (xb::int)/real (yb::int) \<and> yb\<noteq>0" 
    by (force simp add: rats_int_intnot0)

  ultimately have yn0: "y\<noteq>0" and ybn0: "yb\<noteq>0" 
    and eq: "a+b = real x/real y + real xb/real yb" 
    by auto

  note eq also from yn0 ybn0 
  have "\<dots> = real yb * real x / (real yb * real y) + 
    real y * real xb / (real yb * real y)" (is "_ = ?X/?Z + ?Y/?Z")
    by (simp add: real_mult_commute)
  also have "\<dots> = (?X + ?Y)/?Z"
    by (rule add_divide_distrib[THEN sym])
  also have "\<dots> = real (yb*x + y*xb) / real (yb*y)" 
    by (simp only: real_of_int_mult real_of_int_add)

  finally show ?thesis by (simp only: int_int_rats) 
qed


text {*The density proof was first to be adapted from a Mizar document
  \cite{basrat}. 
  Alas, it depends on a
  Gauss bracket (or floor function) that could not be found
  anywhere in Isabelle/HOL; and
  it turned out many lemmata are missing about the relation between
  integers and reals. Fortunately, a much more
  elementary proof was discovered in ``Real Analysis'' by H.L. Royden
  (\cite{Royden1968} p. 32 ff). 
  It directly employs
  the axiom of Archimedes, which is already in the \mbox{@{text RComplete}} theory.*}

lemma assumes nn: "0\<le>x" and ord: "x<y"
  shows rats_dense_in_nn_real: "\<exists>r \<in> \<rat>.  x<r \<and> r<y"
proof -
  from ord have "0 < y-x" by simp
  with reals_Archimedean obtain q::nat 
    where q: "inverse (real q) < y-x" and qpos: "0 < real q"
    by auto
  
  def p \<equiv> "LEAST n.  y \<le> real (Suc n)/real q"
  
  from reals_Archimedean2 obtain n::nat where "y * real q < real n"
    by auto
  with qpos have ex: "y \<le> real n/real q" (is "?P n")
    by (simp add: pos_less_divide_eq[THEN sym])
  also from nn ord have "\<not> y \<le> real (0::nat) / real q" 
    by simp
  ultimately have main: "(LEAST n. y \<le> real n/real q) = Suc p" 
    by (unfold p_def) (rule Least_Suc)
  also from ex have "?P (LEAST x. ?P x)" 
    by (rule LeastI)
  ultimately have suc: "y \<le> real (Suc p) / real q" 
    by simp

  def r \<equiv> "real p/real q"
  
  have "x=y-(y-x)" 
    by simp
  also from suc q have "\<dots> < real (Suc p)/real q - inverse (real q)" 
    by arith
  also have "\<dots> = real p / real q"
    by (simp only: inverse_eq_divide real_diff_def real_of_nat_Suc 
    minus_divide_left add_divide_distrib[THEN sym]) simp
  finally have 1: "x<r" 
    by (unfold r_def)

  have "p<Suc p" .. also note main[THEN sym]
  finally have "\<not> ?P p"  
    by (rule not_less_Least)
  hence 2: "r<y" 
    by (simp add: r_def)
  
  from r_def have "r \<in> \<rat>" 
    by (simp only: nat_nat_rats)
txt{*\nopagebreak*}
  with 1 2 show ?thesis by fast
qed  
  
theorem assumes ord: "x<y"
  shows rats_dense_in_real: "\<exists>r \<in> \<rat>.  x<r \<and> r<y"
proof -
  from reals_Archimedean2 obtain n::nat where "-x < real n" 
    by auto
  hence "0 \<le> x + real n" 
    by arith
  also from ord have "x + real n < y + real n" 
    by arith
  ultimately have "\<exists>r \<in> \<rat>. x + real n < r \<and> r < y + real n"
    by  (rule rats_dense_in_nn_real) 
  then obtain r where r1: "r \<in> \<rat>" and r2: "x + real n < r" 
    and r3: "r < y + real n" 
    by blast
  have "r - real n = r + real (int n)/real (-1::int)" 
    by (simp add: real_of_int_real_of_nat)
  also from r1 have "r + real (int n)/real (-1::int) \<in> \<rat>" 
    by (simp only: int_int_rats rats_plus_rats)
  also from r2 have "x < r - real n" 
    by arith
  moreover from r3 have "r - real n < y" 
    by arith
  
  ultimately show ?thesis 
    by fast
qed
    (*This wraps up the most essential properties of the rational numbers,
    though there are many more to establish, of course *)
end
