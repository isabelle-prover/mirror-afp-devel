(*
   Mike Stannett
   Feb 2023
*)

section \<open> LinearMaps \<close>

text \<open>This theory defines linear maps and establishes their main properties. \<close>

theory LinearMaps
  imports Functions CauchySchwarz Matrices
begin


class LinearMaps = Functions + CauchySchwarz + Matrices
begin

(*
  These functions are all single-valued, so we define them
  as having type ('a Point \<Rightarrow> 'a Point). We can use the
  asFunc function to convert them to relational form
  where necessary.
*)



(* This definition contains unnecessary terms, but this makes
it simpler to use it below. *)
abbreviation linear :: "('a Point \<Rightarrow> 'a Point) \<Rightarrow> bool" where
"linear L \<equiv> (L origin = origin)
          \<and> (\<forall> a p .  L (a \<otimes> p) = (a \<otimes> (L p)))
          \<and> (\<forall> p q . L (p \<oplus> q) = ((L p) \<oplus> (L q)))
          \<and> (\<forall> p q . L (p \<ominus> q) = ((L p) \<ominus> (L q)))"



(* ****************************************************************** *)
(* LEMMAS *)

(* Used to enable explicit substitutions *)
lemma lemLinearProps:                                             
  assumes "linear L"
  shows "(L origin = origin) \<and> (L (a \<otimes> p) = (a \<otimes> (L p))) 
            \<and> (L (p \<oplus> q) = ((L p) \<oplus> (L q)))
                \<and> (L (p \<ominus> q) = ((L p) \<ominus> (L q)))"
using assms by simp



lemma lemMatrixApplicationIsLinear: "linear (applyMatrix m)"
  using lemDotScaleRight lemDotSumRight lemDotDiffRight 
  by fastforce


lemma lemLinearIsMatrixApplication:
  assumes "linear L"
  shows   "\<exists> m . L = (applyMatrix m)"
proof -
  define Lt where "Lt = L tUnit"
  define Lx where "Lx = L xUnit"
  define Ly where "Ly = L yUnit"
  define Lz where "Lz = L zUnit"
  define M  where "M = transpose \<lparr> trow = Lt, xrow = Lx, yrow = Ly, zrow = Lz \<rparr>"

  have trowM: "trow M = \<lparr> tval = (tval Lt), xval = (tval Lx),
                         yval = (tval Ly), zval = (tval Lz) \<rparr>" 
    using M_def by auto
  have xrowM: "xrow M = \<lparr> tval = (xval Lt), xval = (xval Lx),
                         yval = (xval Ly), zval = (xval Lz) \<rparr>" 
    using M_def by auto
  have yrowM: "yrow M = \<lparr> tval = (yval Lt), xval = (yval Lx),
                         yval = (yval Ly), zval = (yval Lz) \<rparr>" 
    using M_def by auto
  have zrowM: "zrow M = \<lparr> tval = (zval Lt), xval = (zval Lx),
                         yval = (zval Ly), zval = (zval Lz) \<rparr>" 
    using M_def by auto


  { fix u :: "'a Point"
    define tvu where tvu: "tvu = ((tval u)\<otimes>tUnit)"
    define xvu where xvu: "xvu = ((xval u)\<otimes>xUnit)"
    define yvu where yvu: "yvu = ((yval u)\<otimes>yUnit)"
    define zvu where zvu: "zvu = ((zval u)\<otimes>zUnit)"

    have u: "u = (tvu \<oplus> (xvu \<oplus> (yvu \<oplus> zvu)))"
      using tvu xvu yvu zvu lemPointDecomposition[of "u"] by simp

    (* Calculate (M u) *)
    have Mu: "applyMatrix M u = \<lparr> tval = dot (trow M) u,
                        xval = dot (xrow M) u,
                        yval = dot (yrow M) u,
                        zval = dot (zrow M) u \<rparr>" by simp

    have tvalMu: "tval (applyMatrix M u) = 
       (tval Lt)*(tval u) + (tval Lx)*(xval u) + (tval Ly)*(yval u) + (tval Lz)*(zval u)"
      using Mu trowM by force
    have xvalMu: "xval (applyMatrix M u) = 
       (xval Lt)*(tval u) + (xval Lx)*(xval u) + (xval Ly)*(yval u) + (xval Lz)*(zval u)"
      using Mu xrowM by force
    have yvalMu: "yval (applyMatrix M u) = 
       (yval Lt)*(tval u) + (yval Lx)*(xval u) + (yval Ly)*(yval u) + (yval Lz)*(zval u)"
      using Mu yrowM by force
    have zvalMu: "zval (applyMatrix M u) = 
       (zval Lt)*(tval u) + (zval Lx)*(xval u) + (zval Ly)*(yval u) + (zval Lz)*(zval u)"
      using Mu zrowM by force

    (* Calculate (L u) *)
    hence Lu: "L u  = ((L tvu) \<oplus> ((L xvu) \<oplus> ((L yvu) \<oplus> (L zvu))))"
      using assms u
            lemLinearProps[of "L" "0" "tvu" "xvu \<oplus> (yvu \<oplus> zvu)"]
            lemLinearProps[of "L" "0" "xvu" "yvu \<oplus> zvu"]
      by auto
    have Ltvu: "L tvu = ((tval u)\<otimes>Lt)" 
      using tvu Lt_def assms lemLinearProps[of "L" "tval u" "tUnit"] by auto
    have Lxvu: "L xvu = ((xval u)\<otimes>Lx)" 
      using xvu Lx_def assms lemLinearProps[of "L" "xval u" "xUnit"] by auto
    have Lyvu: "L yvu = ((yval u)\<otimes>Ly)" 
      using yvu Ly_def assms lemLinearProps[of "L" "yval u" "yUnit"] by auto
    have Lzvu: "L zvu = ((zval u)\<otimes>Lz)" 
      using zvu Lz_def assms lemLinearProps[of "L" "zval u" "zUnit"] by auto

    hence Lu': "L u = (((tval u)\<otimes>Lt) \<oplus> (((xval u)\<otimes>Lx) 
                        \<oplus> (((yval u)\<otimes>Ly) \<oplus> ((zval u)\<otimes>Lz))))"
      using Lu Ltvu Lxvu Lyvu Lzvu by force
  
    hence "L u = applyMatrix M u"  
      using Lu' add_assoc tvalMu xvalMu yvalMu zvalMu mult_commute by simp
  }
  hence "\<forall> u. L u = applyMatrix M u" by auto
  thus ?thesis by force
qed



lemma lemLinearIffMatrix: "linear L \<longleftrightarrow> (\<exists> M. L = applyMatrix M)"
  using lemMatrixApplicationIsLinear lemLinearIsMatrixApplication 
  by auto



lemma lemIdIsLinear: "linear id"
  by simp



lemma lemLinearIsBounded:
  assumes "linear L"
  shows   "bounded L"
proof -
  obtain M where M: "L = applyMatrix M" using assms lemLinearIffMatrix by auto
  define tr where "tr = trow M"
  define xr where "xr = xrow M"
  define yr where "yr = yrow M"
  define zr where "zr = zrow M"
  define bnd where "bnd = (sqr(norm tr)+sqr(norm xr)+sqr(norm yr)+sqr(norm zr))"

  define n 
    where n: "n = \<lparr> tval=norm tr, xval=norm xr, yval=norm yr, zval=norm zr \<rparr>"
  hence "bnd = dot n n" using bnd_def  by auto
  hence norm2n: "bnd = norm2 n" by simp
  hence bndnonneg: "bnd \<ge> 0" by simp

  { assume bndpos: "bnd > 0"
    { fix p :: "'a Point"
  
      define q where "q = applyMatrix M p"
      hence "q = \<lparr> tval=dot tr p, xval=dot xr p,yval=dot yr p, zval=dot zr p \<rparr>"
        using tr_def xr_def yr_def zr_def by auto
      hence 1: "dot q q = sqr (dot tr p) + sqr (dot xr p) 
                          + sqr (dot yr p) + sqr(dot zr p)"
        by auto
      also have "\<dots> \<le> sqr (dot tr p) + sqr (dot xr p) + sqr (dot yr p) 
                        + (sqr(norm zr)*sqr(norm p))"
        using lemCauchySchwarzSqr4[of "zr" "p"]  lemNormSqrIsNorm2 by auto
      also have "\<dots> \<le> sqr (dot tr p) + sqr (dot xr p) + (sqr(norm yr)*sqr(norm p)) 
                        + (sqr(norm zr)*sqr(norm p))"
        using lemCauchySchwarzSqr4[of "yr" "p"]  lemNormSqrIsNorm2 by auto
      also have "\<dots> \<le> sqr (dot tr p) + (sqr(norm xr)*sqr(norm p)) + (sqr(norm yr)*sqr(norm p)) 
                        + (sqr(norm zr)*sqr(norm p))"
        using lemCauchySchwarzSqr4[of "xr" "p"]  lemNormSqrIsNorm2 by auto
      also have "\<dots> \<le> (sqr(norm tr)*sqr(norm p)) + (sqr(norm xr)*sqr(norm p)) + (sqr(norm yr)*sqr(norm p)) 
                        + (sqr(norm zr)*sqr(norm p))"
        using lemCauchySchwarzSqr4[of "tr" "p"]  lemNormSqrIsNorm2 by auto
      finally have "dot q q \<le> (sqr(norm tr)*sqr(norm p)) + (sqr(norm xr)*sqr(norm p)) + (sqr(norm yr)*sqr(norm p)) 
                        + (sqr(norm zr)*sqr(norm p))" by auto
      hence "dot q q \<le> (sqr(norm tr)+sqr(norm xr)+sqr(norm yr)+sqr(norm zr))*sqr(norm p)"
        using distrib_right by auto
      hence "norm2 q \<le> bnd * sqr(norm p)" using bnd_def by simp
      hence "norm2 (applyMatrix M p) \<le> bnd * norm2 p"
        using q_def lemNormSqrIsNorm2  by simp
    }
    hence "\<forall> p. norm2 (applyMatrix M p) \<le> bnd * norm2 p" by auto
    hence "\<exists> bnd > 0 . \<forall> p. norm2 (applyMatrix M p) \<le> bnd * norm2 p" 
      using bndpos by auto
  }
  hence case1: "(bnd > 0) \<longrightarrow> (bounded (applyMatrix M))" by simp

  { assume bnd0: "bnd = 0"
    hence "n = origin" using lemNullImpliesOrigin norm2n by auto
    hence "(norm tr = 0) \<and> (norm xr = 0) \<and> (norm yr = 0) \<and> (norm zr = 0)"
      using n by simp
    hence allzero: "(tr = origin)\<and>(xr=origin)\<and>(yr=origin)\<and>(zr=origin)"
      using lemZeroNorm by auto  
   
    define one where "one = (1::'a)"
    hence onepos: "one > 0" by simp
    { fix p :: "'a Point"
      have "applyMatrix M p = origin" 
        using allzero tr_def xr_def yr_def zr_def by auto
      hence "norm2(applyMatrix M p) = 0" by auto
      hence "norm2(applyMatrix M p) \<le> one * (norm2 p)" using onepos by auto
    }
    hence "\<forall> p .  norm2(applyMatrix M p) \<le> one * (norm2 p)" by auto
    hence "\<exists> one > 0 . \<forall> p .  norm2(applyMatrix M p) \<le> one * (norm2 p)"
      using onepos by auto
    hence "bounded (applyMatrix M)" by simp
  }
  hence case2: "(bnd = 0) \<longrightarrow> (bounded (applyMatrix M))" by simp

  thus ?thesis using case1 case2 bndnonneg M by auto
qed



lemma lemLinearIsCts:
  assumes "linear L"
  shows   "cts (asFunc L) x"
proof -
  { fix x' 
    assume x': "x' = L x"

    have "bounded L" using assms(1) lemLinearIsBounded[of "L"] by auto
    then obtain bnd where bnd: "(bnd > 0) \<and> (\<forall>p. norm2(L p) \<le> bnd*(norm2 p))"
      by auto
    then obtain bb where bb: "(bb > 0) \<and> (sqr bb) > bnd" 
      using bnd lemSquareExistsAbove[of "bnd"] by auto
  
    { fix p
      have p1: "norm2 (L p) \<le> bnd*(norm2 p)" using bnd by simp
      have "bnd*(norm2 p) \<le> (sqr bb)*(norm2 p)" using bb mult_mono by auto
      hence "norm2 (L p) \<le> (sqr bb)*(norm2 p)" using p1 by simp
    }
    hence bbbnd: "\<forall>p . norm2 (L p) \<le> (sqr bb)*(norm2 p)" by auto
   
    { fix e
      assume epos: "e > 0"
      define d where d: "d = e/bb"
      hence dpos: "d > 0" using epos bb by simp
      have "(d = e/bb) \<and> (bb \<noteq> 0)" using d bb by auto
      hence esqr: "(sqr d)*(sqr bb) = sqr e" by simp
  
  
      { fix p'
        assume p': "p' \<in> applyToSet (asFunc L) (ball x d)"
        then obtain p where p: "(p \<in> ball x d) \<and> (p' = L p)" by auto
        hence p_near_x: "p within d of x" using lemSep2Symmetry[of "p" "x"] by force
  
        have "norm2 (L (p\<ominus>x)) \<le> (sqr bb) * norm2 (p\<ominus>x)" using bbbnd by blast
        hence 1: "norm2 (L (p\<ominus>x)) \<le> (sqr bb) * (sep2 p x)" by auto
        have "(sqr bb)*(sep2 p x) < (sqr bb)*(sqr d)"
          using lemMultPosLT bb p_near_x by auto
        hence 2: "norm2 (L (p\<ominus>x)) < (sqr bb) * (sqr d)" using 1  by simp
                        
        have "(L (p\<ominus>x)) = ((L p) \<ominus> (L x))" using assms(1) by auto
        hence "norm2 (L (p\<ominus>x)) = sep2 p' x'" using p x' by force
        hence "sep2 p' x' <  (sqr bb) * (sqr d)" using 2 by simp
        hence "sep2 p' x' <  sqr e" using d bb by auto
        hence "p' \<in> ball x' e" using lemSep2Symmetry by auto
      }
      hence "applyToSet (asFunc L) (ball x d) \<subseteq> ball x' e" by auto
      hence "\<exists>d>0. applyToSet (asFunc L) (ball x d) \<subseteq> ball x' e" 
        using dpos by auto
    }
    hence "\<forall>e>0. \<exists>d>0. applyToSet (asFunc L) (ball x d) \<subseteq> ball x' e" 
      by auto
  }
  thus ?thesis by auto
qed


lemma lemLinOfLinIsLin:
assumes "(linear A) \<and> (linear B)"
shows   "linear (B \<circ> A)"
proof -
  have 1: "(B \<circ> A) origin = origin" using assms by auto
  have 2: "\<forall> a p . (B \<circ> A)(a \<otimes> p) = (a \<otimes> ((B \<circ> A) p))" using assms by auto
  have 3: "\<forall> p q . (B \<circ> A) (p \<oplus> q) = (((B \<circ> A) p) \<oplus> ((B \<circ> A) q))" using assms by auto
  have 4: "\<forall> p q . (B \<circ> A) (p \<ominus> q) = (((B \<circ> A) p) \<ominus> ((B \<circ> A) q))" using assms by auto
  thus ?thesis using 1 2 3 by force
qed



lemma lemInverseLinear:
  assumes "linear A"
and       "invertible A"
shows     "\<exists>A' . (linear A') \<and> (\<forall> p q. A p = q \<longleftrightarrow> A' q = p)"
proof -
  obtain L where L: "(\<forall> p q. A p = q \<longleftrightarrow> L q = p)" 
    using assms(2) by metis

  have 1: "L origin = origin" using assms L by auto

  { fix p' q' a
    obtain p where p: "(A p = p') \<and> (\<forall>z. A z = p' \<longrightarrow> z = p)" using assms(2) by blast
    obtain q where q: "(A q = q') \<and> (\<forall>z. A z = q' \<longrightarrow> z = q)" using assms(2) by blast

    have "L (a \<otimes> p') = L ( a \<otimes> (A p) )" using p by auto
    also have "... = L ( A ( a \<otimes> p ) )" using assms(1) by auto
    also have "... = (a \<otimes> p)" using L by blast
    finally have 2: "L (a \<otimes> p') = (a \<otimes> (L p'))" using p L by auto

    have "L (p' \<oplus> q') = L ((A p) \<oplus> (A q))" using p q by auto
    also have "... = L( A (p \<oplus> q) )" using assms(1) by auto
    also have "... = (p \<oplus> q)" using p q L by auto
    finally have 3: "L (p' \<oplus> q') = ( (L p') \<oplus> (L q') )" using p q L by auto

    have "L (p' \<ominus> q') = L ((A p) \<ominus> (A q))" using p q by auto
    also have "... = L( A (p \<ominus> q) )" using assms(1) by auto
    also have "... = (p \<ominus> q)" using p q L by auto
    finally have 4: "L (p' \<ominus> q') = ( (L p') \<ominus> (L q') )" using p q L by auto

    hence "(L origin = origin) \<and>  
           (L (a \<otimes> p') = (a \<otimes> (L p'))) \<and>
           (L (p' \<oplus> q') = ( (L p') \<oplus> (L q') )) \<and> 
           (L (p' \<ominus> q') = ( (L p') \<ominus> (L q') ))"
      using 1 2 3 by auto
  }
  hence "linear L" by auto

  thus ?thesis using L by auto
qed



end (* of class LinearMaps *)


end (* of theory LinearMaps *)
