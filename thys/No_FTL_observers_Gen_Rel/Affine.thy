(*
   Mike Stannett
   Feb 2023
*)

section \<open> Affine \<close>

text \<open>This theory defines affine transformations and established their
key properties.\<close>

theory Affine
  imports Translations LinearMaps
begin


class Affine = Translations + LinearMaps
begin



abbreviation affine :: "('a Point \<Rightarrow> 'a Point) \<Rightarrow> bool" 
  where "affine A \<equiv> \<exists> L T . (linear L) \<and> (translation T) \<and> (A = T \<circ> L)"


abbreviation affInvertible :: "('a Point \<Rightarrow> 'a Point) \<Rightarrow> bool"
  where "affInvertible A \<equiv> affine A \<and> invertible A"


abbreviation isLinearPart :: "('a Point \<Rightarrow> 'a Point) \<Rightarrow> ('a Point \<Rightarrow> 'a Point) \<Rightarrow> bool"
  where "isLinearPart A L \<equiv> (affine A) \<and> (linear L) \<and> 
          (\<exists> T. (translation T \<and> A = T \<circ> L))"

abbreviation isTranslationPart  :: "('a Point \<Rightarrow> 'a Point) \<Rightarrow> ('a Point \<Rightarrow> 'a Point) \<Rightarrow> bool"
  where "isTranslationPart A T \<equiv> (affine A) \<and> (translation T) \<and> 
          (\<exists> L. (linear L \<and> A = T \<circ> L))"

(* affine approximation *)

subsection \<open> Affine approximation \<close>

text \<open>A key concept in the proof is affine approximation. We will eventually 
assert that worldview transformation can be approximated by invertible affine 
transformations.\<close>

abbreviation affineApprox :: "('a Point \<Rightarrow> 'a Point) \<Rightarrow> 
                           ('a Point \<Rightarrow> 'a Point => bool) \<Rightarrow>
                            'a Point \<Rightarrow> bool"
  where "affineApprox A f x \<equiv> (isFunction f) \<and> 
           (affInvertible A) \<and> (diffApprox (asFunc A) f x)"


fun applyAffineToLine :: "('a Point \<Rightarrow> 'a Point) 
                \<Rightarrow> 'a Point set \<Rightarrow> 'a Point set \<Rightarrow> bool"
  where "applyAffineToLine A l l' \<longleftrightarrow> (affine A) \<and> 
    (\<exists> T L b d . ((linear L) \<and> (translation T) \<and> (A = T \<circ> L) \<and>
       (l = line b d) \<and> (l' = (line (A b) (L d)))))"


(* miscellaneous *)

abbreviation affConstantOn ::  "('a Point \<Rightarrow> 'Point) \<Rightarrow> 'a Point \<Rightarrow> 'a Point set \<Rightarrow> bool"
  where "affConstantOn A x s \<equiv> (\<exists>\<epsilon>>0. \<forall>y\<in>s. (y within \<epsilon> of x) \<longrightarrow> ((A y) = (A x)))"


(* ****************************************************************** *)
(* LEMMAS *)

lemma lemTranslationPartIsUnique:
  assumes "isTranslationPart A T1"
and       "isTranslationPart A T2"
shows     "T1 = T2"
proof -
  obtain L1 where T1: "linear L1 \<and> A = T1 \<circ> L1" using assms(1) by auto 
  obtain L2 where T2: "linear L2 \<and> A = T2 \<circ> L2" using assms(2) by auto 
  obtain t1 where t1: "\<forall> x. T1 x = (x \<oplus> t1)" using assms(1) by auto
  obtain t2 where t2: "\<forall> x. T2 x = (x \<oplus> t2)" using assms(2) by auto

  have "T1 origin = A origin" using T1 assms(1) by auto
  also have  "... = T2 origin" using T2 assms(2) by auto
  finally have "T1 origin = T2 origin" by auto
  hence "t1 = t2" using t1 t2 by auto
  hence "\<forall> x. (T1 x = T2 x)" using t1 t2 by auto
  thus ?thesis by auto
qed



lemma lemLinearPartIsUnique:
  assumes "isLinearPart A L1"
and       "isLinearPart A L2"
shows     "L1 = L2"
proof -
  obtain T1 where T1: "translation T1 \<and> A = T1 \<circ> L1" using assms(1) by auto
  obtain T2 where T2: "translation T2 \<and> A = T2 \<circ> L2" using assms(2) by auto

  have 1: "isTranslationPart A T1" using assms(1) T1 by auto
  have 2: "isTranslationPart A T2" using assms(2) T2 by auto
  hence T1T2: "T1 = T2" using 1 2 lemTranslationPartIsUnique[of "A" "T1" "T2"] by auto

  obtain t where t: "\<forall> x. T1 x = (x \<oplus> t)" using T1 by auto
  define T where "T = mkTranslation (origin \<ominus> t)" 
  hence 3: "T \<circ> A = L1" using T1 t lemInverseTranslation by auto
  have "T \<circ> A = L2" using T_def T2 t T1T2 lemInverseTranslation by auto

  thus ?thesis using 3 by auto
qed


lemma lemLinearImpliesAffine:
assumes "linear L"
shows "affine L"
proof - 
  have 1: "L = id \<circ> L" by fastforce
  thus ?thesis using assms lemIdIsTranslation by blast
qed


lemma lemTranslationImpliesAffine:
assumes "translation T"
shows "affine T"
proof - 
  have "T = T \<circ> id" by force
  thus ?thesis using assms lemIdIsLinear by blast
qed


lemma lemAffineDiff:
  assumes "linear L"
and       "\<exists> T . ((translation T) \<and> (A = T \<circ> L))"
  shows "((A p) \<ominus> (A q)) = L (p \<ominus> q)"
proof -
  obtain T where T: "(translation T) \<and> (A = T \<circ> L)" using assms(2) by auto
  thus ?thesis using assms(1) by auto
qed


lemma lemAffineImpliesTotalFunction:
  assumes "affine A"
  shows "isTotalFunction (asFunc A)"
  by simp


lemma lemAffineEqualAtBase:
  assumes "affineApprox A f x"
  shows   "\<forall>y. (f x y) \<longleftrightarrow> (y = A x)"
proof -
  have diff: "diffApprox (asFunc A) f x" using assms(1) by simp
  { fix y
    assume y: "f x y"
    hence "f x y \<and> (asFunc A) x (A x)" by auto
    hence "A x = y" using diff lemApproxEqualAtBase[of "f" "x" "asFunc A" "y"]
      by auto
  }
  hence l2r: "\<forall>y . f x y \<longrightarrow> y = A x" by auto

  { obtain y where y: "f x y" using diff by auto
    hence "y = A x" using l2r by auto
    hence "f x (A x)" using y by auto
  }
  thus ?thesis using l2r by blast
qed


lemma lemAffineOfPointOnLine:
  assumes "(linear L) \<and> (translation T) \<and> (A = T \<circ> L)"
and       "x = (b \<oplus> (a\<otimes>d))"
  shows   "A x = ((A b) \<oplus> (a \<otimes> (L d)))"
proof -
  have "(L x = ((L b) \<oplus> (L (a \<otimes> d)))) \<and> (L (a \<otimes> d) = (a \<otimes> (L d)))" 
    using assms by blast
  hence "A x = T ((L b) \<oplus> (a \<otimes> (L d)))" using assms(1) by auto
  also have "... = ((T (L b)) \<oplus> (a \<otimes> (L d)))" 
    using assms(1) lemTranslationSum[of "T" "L b" "a \<otimes> (L d)"] by auto
  finally show ?thesis using assms(1) by auto
qed



(* applyAffineToLine takes for granted that the image of a line is a line.
   We need to prove that this is true *)
lemma lemAffineOfLineIsLine: 
  assumes "isLine l"
  shows "(applyAffineToLine A l l')  \<longleftrightarrow>  (affine A \<and> l' = applyToSet (asFunc A) l)"
proof - 
  { assume lhs: "applyAffineToLine A l l'"
    hence affA: "affine A" by fastforce
    have "\<exists> T L b d . (linear L) \<and> (translation T) \<and> (A = T \<circ> L) \<and>
       (l = line b d) \<and> (l' = (line (A b) (L d)))" using lhs by auto
    then obtain T L b d where TL: "(linear L) \<and> (translation T) \<and> (A = T \<circ> L) \<and>
       (l = line b d) \<and> (l' = (line (A b) (L d)))"
      using lhs by blast
    { fix p'
      { assume "p' \<in> l'"
        then obtain a where a: "p' = ( (A b) \<oplus> (a \<otimes> (L d)) )" using TL by auto
        define p where p: "p = (b \<oplus> (a\<otimes>d))"
        hence "p' \<in> applyToSet (asFunc A) l" using a TL lemAffineOfPointOnLine by auto
      }
      hence "(p' \<in> l') \<longrightarrow> (p' \<in> applyToSet (asFunc A) l)" by auto
    }
    hence l2r: "l' \<subseteq> (applyToSet (asFunc A) l)" by auto

    { fix p'
      { assume "p' \<in> applyToSet (asFunc A) l"
        then obtain p where p: "p \<in> l \<and> p' = A p" by auto
        then obtain a where a: "p = (b \<oplus> (a\<otimes>d))" using TL by auto
        hence "A p = ((A b) \<oplus> (a \<otimes> (L d)))" using TL lemAffineOfPointOnLine by auto
        hence "p' \<in> l'" using TL p by auto
      }
      hence "(p' \<in> applyToSet (asFunc A) l) \<longrightarrow> (p' \<in> l')" using l2r by auto
    }
    hence "(applyToSet (asFunc A) l) \<subseteq> l'" by auto
    hence "affine A \<and> l' = applyToSet (asFunc A) l" using affA l2r by auto
  }
  hence rtp1: "(applyAffineToLine A l l') \<longrightarrow> (affine A \<and> l' = applyToSet (asFunc A) l)"
    by blast

  { assume rhs: "(affine A) \<and> (l' = applyToSet (asFunc A) l)"

    obtain b d where bd: "l = line b d" using assms(1) by auto
    obtain T L where TL: "(linear L) \<and> (translation T) \<and> (A = T \<circ> L)"
      using rhs by auto

    { fix p'
      assume "p' \<in> l'"
      then obtain p where p: "(p \<in> l) \<and> (A p = p')" using rhs by auto
      then obtain a where a: "p = (b \<oplus> (a\<otimes>d))" using bd by auto
      hence "A p = ((A b) \<oplus> (a \<otimes> (L d)))" 
        using TL lemAffineOfPointOnLine by auto
      hence "p' \<in> line (A b) (L d)" using  p by auto
    }
    hence l2r: "l' \<subseteq> line (A b) (L d)" by force

    { fix p'
      assume "p' \<in> line (A b) (L d)"
      then obtain a where a: "p' = ( (A b) \<oplus> (a \<otimes> (L d)) )" using TL by auto
      define p where p: "p = (b \<oplus> (a\<otimes>d))"
      hence "A p = ((A b) \<oplus> (a \<otimes> (L d)))" 
        using TL lemAffineOfPointOnLine by auto
      hence "A p = p'" using a by simp
      hence "p' \<in> applyToSet (asFunc A) l" using p bd by auto
    }
    hence "line (A b) (L d) = l'" using rhs l2r by blast

    hence "applyAffineToLine A l l'" using TL bd by auto
  }
  hence "(affine A) \<and> (l' = applyToSet (asFunc A) l) 
                   \<longrightarrow> (applyAffineToLine A l l')"
    by blast

  thus ?thesis using rtp1 by blast
qed
      
      

lemma lemOnLineUnderAffine:
  assumes "(affine A) \<and> (onLine p l)"
shows     "onLine (A p) (applyToSet (asFunc A) l)"
proof -

  define l' where l': "l' = applyToSet (asFunc A) l"
  have lineL: "isLine l" using assms by auto

  hence Tll': "applyAffineToLine A l l'" 
    using lemAffineOfLineIsLine[of "l" "A" "l'"] assms l'
    by blast
  hence "\<exists> T' L b d . (linear L) \<and> (translation T') \<and> (A = T' \<circ> L) \<and>
       (l = line b d) \<and> (l' = (line (A b) (L d)))" by force
  then obtain T' L b d 
    where TLbd: "(linear L) \<and> (translation T') \<and> (A = T' \<circ> L) \<and>
       (l = line b d) \<and> (l' = (line (A b) (L d)))" by blast
  then obtain a where a: "p = (b \<oplus> (a\<otimes>d))" using assms by auto

  hence "A p = ((A b) \<oplus> (a \<otimes> (L d)))" using lemAffineOfPointOnLine TLbd by auto
  thus ?thesis using l' TLbd by blast
qed



lemma lemLineJoiningUnderAffine:
  assumes "affine A"
  shows   "applyToSet (asFunc A) (lineJoining p q) = lineJoining (A p) (A q)"
proof - 
  obtain T L where TL: "translation T \<and> linear L \<and> A = T\<circ>L" using assms(1) by auto
  hence "((A q) \<ominus> (A p)) = L (q\<ominus>p)" by auto

  { fix a
    have "(a\<otimes>((A q) \<ominus> (A p))) = L (a \<otimes> (q\<ominus>p))" 
      using TL lemLinearProps[of "L" "a" "q\<ominus>p"] by force
  }
  hence as: "\<forall>a. (a\<otimes>((A q) \<ominus> (A p))) = L (a \<otimes> (q\<ominus>p))" by auto

  { fix x'
    assume "x' \<in> applyToSet (asFunc A) (lineJoining p q)"
    then obtain x where x: "x \<in> (lineJoining p q) \<and> x' = A x" by force
    then obtain a where a: "x = (p \<oplus> (a\<otimes>(q\<ominus>p)))" by force

    have expandL: "L (p \<oplus> (a\<otimes>(q\<ominus>p))) = ((L p) \<oplus> (L (a\<otimes>(q\<ominus>p))))" 
      using TL lemLinearProps[of "L" "0" "p" "(a\<otimes>(q\<ominus>p))"]     
      by fast

    have "x' = A (p \<oplus> (a\<otimes>(q\<ominus>p)))" using x a by fast
    also have "... = (T (L (p \<oplus> (a\<otimes>(q\<ominus>p)))))" using TL by force
    also have "... = T ((L p) \<oplus> (L (a\<otimes>(q\<ominus>p))))" using expandL by force
    finally have "x' = ((T (L p)) \<oplus> (L (a\<otimes>(q\<ominus>p))))"
      using TL lemTranslationSum[of "T" "L p" "L (a\<otimes>(q\<ominus>p))"]
      by auto
    hence "x' \<in> lineJoining (A p) (A q)" using TL as by auto
  }
  hence l2r: "applyToSet (asFunc A) (lineJoining p q) \<subseteq> lineJoining (A p) (A q)" 
    by force

  { fix x'
    assume "x' \<in> lineJoining (A p) (A q)"
    hence "\<exists>a . x' = ((T (L p)) \<oplus> (a\<otimes>((A q)\<ominus>(A p))))" 
      using TL by auto
    then obtain a where a: "x' = ((T (L p)) \<oplus> (a\<otimes>((A q)\<ominus>(A p))))" 
      using TL by fast
    hence "x' = ((T (L p)) \<oplus> (L (a\<otimes>(q\<ominus>p))))" using as by force
    also have "... = T ( (L p) \<oplus> (L (a\<otimes>(q\<ominus>p))))" 
      using TL lemTranslationSum[of "T" "L p" "L (a\<otimes>(q\<ominus>p))"] by simp
    also have "... = T ( L (p \<oplus> (a\<otimes>(q\<ominus>p))) )"
      using TL lemLinearProps[of "L" "0" "p" "a\<otimes>(q\<ominus>p)"] by auto
    finally have "x' = A (p \<oplus> (a\<otimes>(q\<ominus>p)))" using TL by auto
    hence "x' \<in> applyToSet (asFunc A) (lineJoining p q)" by auto
  }
  thus ?thesis using l2r by auto
qed




lemma lemAffineIsCts:
  assumes "affine A"
  shows   "cts (asFunc A) x"
proof -
  
  have "\<exists> T L . (translation T)\<and>(linear L)\<and>(A = T \<circ> L)" using assms by auto
  then obtain T L where TL: "(translation T)\<and>(linear L)\<and>(A = T \<circ> L)" by auto

  define f where f: "f = asFunc L"
  define g where g: "g = asFunc T"
  have 1: "cts f x" using f TL lemLinearIsCts[of "L" "x"] by auto
  have 2: "\<forall>y. (f x y) \<longrightarrow> (cts g y)" 
    using f g TL lemTranslationIsCts[of "T" "x"] by auto
  have "cts (composeRel g f) x" using 1 2 lemCtsOfCtsIsCts[of "f" "x" "g"] by simp
  thus ?thesis using f g TL by auto
qed

 
lemma lemAffineContinuity:
  assumes "affine A"
  shows "\<forall> x. \<forall>\<epsilon>>0. \<exists>\<delta>>0 . \<forall>p. (p within \<delta> of x) \<longrightarrow> ((A p) within \<epsilon> of (A x))"
proof -
  { fix x 
    { fix e
      assume epos: "e > 0"
  
      have "(asFunc A) x (A x) \<and> (cts (asFunc A) x)" 
        using assms lemAffineIsCts[of "A" "x"] by auto
      hence u: "(\<forall>\<epsilon>>0. \<exists>\<delta>>0. (applyToSet (asFunc A) (ball x \<delta>)) \<subseteq> ball (A x) \<epsilon>)"
        by force
      then obtain d where d: "(d > 0) \<and> 
                            (applyToSet (asFunc A) (ball x d)) \<subseteq> ball (A x) e"
        using epos by force
  
      { fix p
        assume "p within d of x"
        hence "(A p) within e of (A x)" using d lemSep2Symmetry by force
      }
      hence "\<exists>d>0 . \<forall>p. (p within d of x) \<longrightarrow> ((A p) within e of (A x))"
        using d by auto
    }
    hence "\<forall>e>0. \<exists>d>0 . \<forall>p. (p within d of x) \<longrightarrow> ((A p) within e of (A x))"
      by auto
  }
  thus ?thesis by auto
qed


lemma lemAffOfAffIsAff:
  assumes "(affine A) \<and> (affine B)"
shows     "affine (B \<circ> A)"
proof - 
  obtain TA LA TB LB where props: 
            "translation TA \<and> linear LA \<and> translation TB \<and> linear LB \<and>
                 A = TA \<circ> LA  \<and>  B = TB \<circ> LB" using assms by blast
  then obtain ta tb where ts: "(\<forall>p. TA p = (p \<oplus> ta)) \<and> (\<forall>p. TB p = (p \<oplus> tb))" by auto

  { fix p
    have "(B \<circ> A) p = ((LB ( (LA p) \<oplus> ta )) \<oplus> tb)" using props ts by force
    also have "... = (((LB (LA p)) \<oplus> (LB ta)) \<oplus> tb)" using props by force
    also have "... = (((LB\<circ>LA) p) \<oplus> ((LB ta)\<oplus>tb))" using add_assoc by force
    finally have "(B \<circ> A) p = ((mkTranslation ((LB ta)\<oplus>tb)) \<circ> (LB\<circ>LA)) p" by force
  }
  hence BA: "(B \<circ> A) = (mkTranslation ((LB ta)\<oplus>tb)) \<circ> (LB\<circ>LA)" by auto

  define T where T: "T = mkTranslation ((LB ta)\<oplus>tb)"
  hence trans: "translation T" using lemMkTrans by blast
  define L where L: "L = (LB\<circ>LA)"
  hence lin: "linear L" using lemLinOfLinIsLin[of "LA" "LB"] props by auto

  hence "(translation T) \<and> (linear L) \<and> ((B\<circ>A) = (T\<circ>L))" using T L trans lin BA by auto
  thus ?thesis by auto
qed



lemma lemInverseAffine:
  assumes "affInvertible A"
shows     "\<exists>A' . (affine A') \<and> (\<forall> p q . A p = q \<longleftrightarrow> A' q = p)"
proof -
  obtain A' where A': "(\<forall> p q. A p = q \<longleftrightarrow> A' q = p)" 
    using assms by metis

(*  Have A = T o L,  so want to show that  A' =  L' o T' 

    First have to show that L is invertible, so we can obtain linear L'.
    Use the fact that L = T' o A.
*)
  obtain T L where TL: "translation T \<and> linear L \<and> (A = T \<circ> L)" using assms(1) by auto

  obtain T' where T': "(translation T') \<and> (\<forall> p q . T p = q \<longleftrightarrow> T' q = p)" 
    using TL lemInverseTrans[of "T"] by auto

  { fix p
    { fix q
      assume Ap: "A p = q"
      hence  "T (L p) = q" using TL by auto
      hence  "L p = T' q" using T' by auto
      hence  "L  p = (T' \<circ> A) p" using Ap by auto
    }
  }
  hence L: "L = (T' \<circ> A)" by auto

  { fix q
    obtain r where r: "(T' r = q)" using T' by auto
    then obtain p where p: "(A p = r) \<and> (\<forall>x. A x = r \<longrightarrow> x = p)" using A' by auto
    hence 1: "L p = q" using L r by auto
    { fix x
      assume "L x = q"
      hence "T' (A x) = q" using L by auto
      hence "A x = r" using r T' lemTranslationInjective[of "T'"] by force
      hence "x = p" using p A' by blast
    } hence "\<exists>p . (L p = q) \<and> (\<forall>x. L x = q \<longrightarrow> x = p)" using 1 by auto
  }
  hence invL: "invertible L" by blast

  then obtain L' where L': "(linear L') \<and> (\<forall> p q . L p = q \<longleftrightarrow> L' q = p)" 
    using TL lemInverseLinear[of "L"] by blast

  (* Main section of proof *)
  { fix p q
    have "A' q = p  \<longleftrightarrow>  T (L p) = q" using A' TL by auto
    also have "...  \<longleftrightarrow>  T' q = L p" using T' by auto
    also have "...  \<longleftrightarrow>  L p = T' q" by auto
    also have "...  \<longleftrightarrow>  L' (T' q) = p" using L' by auto
    finally have "A' q = p  \<longleftrightarrow>  (L'\<circ>T') q = p" by auto
  }
  hence "A' = L' \<circ> T'" by auto
  hence "affine A'" using lemAffOfAffIsAff[of "T'" "L'"]
                          lemTranslationImpliesAffine[of "T'"] T'
                          lemLinearImpliesAffine[of "L'"] L'
    by auto

  thus ?thesis using A' by auto
qed



lemma lemAffineApproxDomainTranslation:
  assumes "translation T"
and       "affineApprox A f x"
and       "\<forall> p q . T p = q  \<longleftrightarrow>  T' q = p"
shows     "affineApprox (A\<circ>T) (composeRel f (asFunc T)) (T' x)"
proof -

  define A0 where A0: "A0 = A \<circ> T"
  define g where g: "g = composeRel f (asFunc T)"

  have ToT': "\<forall> p . T (T' p) = p" using assms(3) by force
  have T'oT: "\<forall> p . T' (T p) = p" using assms(3) by force
  obtain t where t: "\<forall> p . T p = (p \<oplus> t)" using assms(1) by force 
  hence mkT: "T = mkTranslation t" by force

  { fix p q
    have "T' p = q  \<longleftrightarrow>  T q = p" using assms(3) by auto
    also have "... \<longleftrightarrow> (q \<oplus> t) = p" using t by auto
    also have "... \<longleftrightarrow> q = (p \<oplus> (origin \<ominus> t))" by force
    finally have "T' p = q  \<longleftrightarrow>  q = (p \<oplus> (origin \<ominus> t))" by force
    hence "T' p = q  \<longleftrightarrow>  q = mkTranslation (origin \<ominus> t) p" by force
  }
  hence mkT': "T' = mkTranslation (origin \<ominus> t)" by force
  hence transT': "translation T'" using lemMkTrans by blast

  (* 3a: isFunction g *)
  have funcF: "isFunction f" using assms(2) by auto
  hence rtp3a: "isFunction g" using g by auto

  (* 3b: affine A0 *)
  have affA: "affine A" using assms(2)  by auto
  hence rtp3b: "affine A0" 
    using lemAffOfAffIsAff[of "T" "A"] lemTranslationImpliesAffine[of "T"]
          A0 affA assms(1)
    by blast

  (* 3c: invertible A0 *)
  { fix q
    obtain p where p: "(A p = q) \<and> (\<forall>x. A x = q \<longrightarrow> x = p)" using assms(2) by blast
    define p0 where p0: "p0 = T' p"
    hence Tp0: "T p0 = p" using assms(3) by blast
    hence 1: "A0 p0 = q" using A0 p by auto
    { fix x
      assume "A0 x = q"
      hence  "T x = p" using A0 p by fastforce
      hence  "x = p0" using Tp0 assms(1) lemTranslationInjective[of "T"] by force
    }
    hence "\<forall>x. A0 x = q \<longrightarrow> x = p0" by auto

    hence "\<exists>p0. (A0 p0 = q) \<and> (\<forall>x. A0 x = q \<longrightarrow> x = p0)" using 1 by auto
  }
  hence rtp3c: "invertible A0" by auto

  (* 3d: diffApprox (asFunc A0) g origin *)
  have "diffApprox (asFunc A) f x" using assms(2) by auto
  hence dAx: "(definedAt f x) \<and>
    (\<forall> \<epsilon> > 0 . (\<exists> \<delta> > 0 . (\<forall> y .
      ( (y within \<delta> of x)
        \<longrightarrow> 
        ( (definedAt f y) \<and> (\<forall> u v . (f y u \<and> (asFunc A) y v) \<longrightarrow>
         ( sep2 v u ) \<le> (sqr \<epsilon>) * sep2 y x )))  )
  ))" by blast
  hence "(definedAt f x) \<and> (x = T (T' x))" using assms(1) ToT' by auto
  hence rtp3d1: "(definedAt g (T' x))" using g by auto 

  { fix e
    assume epos: "e > 0"
    then obtain d where d: "(d > 0) \<and> (\<forall> y .
      ( (y within d of x)
        \<longrightarrow> 
        ( (definedAt f y) \<and> (\<forall> u v . (f y u \<and> (asFunc A) y v) \<longrightarrow>
         ( sep2 v u ) \<le> (sqr e) * sep2 y x )))  )"
      using dAx by force
    { fix y
      assume "y within d of (T' x)"
      hence "(T y) within d of (T (T' x))" using assms(1) lemBallTranslation by auto
      hence "(T y) within d of x" using ToT' by auto
      hence "(definedAt f (T y)) \<and> (\<forall> u v . (f (T y) u \<and> (asFunc A) (T y) v) \<longrightarrow>
         ( sep2 v u ) \<le> (sqr e) * sep2 (T y) x )"
        using d by blast
      hence "(definedAt g y) \<and> (\<forall> u v . (g y u \<and> (asFunc A0) y v) \<longrightarrow>
         ( sep2 v u ) \<le> (sqr e) * sep2 (T y) x )" using g A0 by auto
      hence "(definedAt g y) \<and> (\<forall> u v . (g y u \<and> (asFunc A0) y v) \<longrightarrow>
         ( sep2 v u ) \<le> (sqr e) * sep2 y (T' x) )" 
        using transT' lemTranslationPreservesSep2[of "T'" "T y" "x"]  T'oT
        by auto
    }
    hence "\<exists>d > 0. \<forall>y . (y within d of (T' x)) \<longrightarrow> 
             (definedAt g y) \<and> (\<forall> u v . (g y u \<and> (asFunc A0) y v) \<longrightarrow>
                   ( sep2 v u ) \<le> (sqr e) * sep2 y (T' x) )"
      using d by fast
  }
  hence rtp3d2: "\<forall>e>0. \<exists>d > 0. \<forall>y . (y within d of (T' x)) \<longrightarrow> 
             (definedAt g y) \<and> (\<forall> u v . (g y u \<and> (asFunc A0) y v) \<longrightarrow>
                   ( sep2 v u ) \<le> (sqr e) * sep2 y (T' x) )"
    by auto
  hence rtp3d: "diffApprox (asFunc A0) g (T' x)" using rtp3d1 by fast

  have rtp3: "affineApprox A0 g (T' x)" using rtp3a rtp3b rtp3c rtp3d by blast

  thus ?thesis using A0 g by fast
qed



lemma lemAffineApproxRangeTranslation:
  assumes "translation T"
and       "affineApprox A f x"
shows     "affineApprox (T\<circ>A) (composeRel (asFunc T) f) x"
proof -

  define A0 where A0: "A0 = T \<circ> A"
  define g where g: "g = composeRel (asFunc T) f"

  obtain T' where T': "(translation T') \<and> (\<forall> p q . T p = q \<longleftrightarrow> T' q = p)"
    using assms(1) lemInverseTrans[of "T"] by auto


  have ToT': "\<forall> p . T (T' p) = p" using T' by force
  have T'oT: "\<forall> p . T' (T p) = p" using T' by force
  obtain t where t: "\<forall> p . T p = (p \<oplus> t)" using assms(1) by auto 
  hence mkT: "T = mkTranslation t" by auto

  { fix p q
    have "T' p = q  \<longleftrightarrow>  T q = p" using T' by auto
    also have "... \<longleftrightarrow> (q \<oplus> t) = p" using t by auto
    also have "... \<longleftrightarrow> q = (p \<oplus> (origin \<ominus> t))" by force
    finally have "T' p = q  \<longleftrightarrow>  q = (p \<oplus> (origin \<ominus> t))" by force
    hence "T' p = q  \<longleftrightarrow>  q = mkTranslation (origin \<ominus> t) p" by force
  }
  hence mkT': "T' = mkTranslation (origin \<ominus> t)" by auto
  hence transT': "translation T'" using lemMkTrans by blast

  (* 3a: isFunction g *)
  have funcF: "isFunction f" using assms(2) by auto
  hence rtp3a: "isFunction g" using g by auto

  (* 3b: affine A0 *)
  have affA: "affine A" using assms(2)  by auto
  hence rtp3b: "affine A0" 
    using lemAffOfAffIsAff[of "A" "T"] lemTranslationImpliesAffine[of "T"]
          A0 affA assms(1)
    by blast

  (* 3c: invertible A0 *)
  { fix q
    obtain p where p: "(A p = T' q) \<and> (\<forall>x. A x = T' q \<longrightarrow> x = p)" using assms(2) by blast
    hence "T' q = A p" by auto
    hence "T (A p) = q" using T' ToT' by auto
    hence 1: "A0 p = q" using A0 by auto

    { fix x
      assume "A0 x = q"
      hence  "T (A x) = q" using A0 by auto
      hence  "T' (T (A x)) = T' q" by auto
      hence  "A x = T' q" using T'oT by auto
      hence  "x = p" using p by auto
    }
    hence "\<forall>x. A0 x = q \<longrightarrow> x = p" by auto

    hence "\<exists>p0. (A0 p0 = q) \<and> (\<forall>x. A0 x = q \<longrightarrow> x = p0)" using 1 by auto
  }
  hence rtp3c: "invertible A0" by auto

  (* 3d: diffApprox (asFunc A0) g origin *)
  have "diffApprox (asFunc A) f x" using assms(2) by auto
  hence dAx: "(definedAt f x) \<and>
    (\<forall> \<epsilon> > 0 . (\<exists> \<delta> > 0 . (\<forall> y .
      ( (y within \<delta> of x)
        \<longrightarrow> 
        ( (definedAt f y) \<and> (\<forall> u v . (f y u \<and> (asFunc A) y v) \<longrightarrow>
         ( sep2 v u ) \<le> (sqr \<epsilon>) * sep2 y x )))  )
  ))" by blast
  hence rtp3d1: "definedAt g x" using g by auto 

  { fix e
    assume epos: "e > 0"
    then obtain d where d: "(d > 0) \<and> (\<forall> y .
      ( (y within d of x)
        \<longrightarrow> 
        ( (definedAt f y) \<and> (\<forall> u v . (f y u \<and> (asFunc A) y v) \<longrightarrow>
         ( sep2 v u ) \<le> (sqr e) * sep2 y x )))  )"
      using dAx by auto
    { fix y
      assume "y within d of x"
      hence "(definedAt f y) \<and> (\<forall> u v . (f y u \<and> (asFunc A) y v) \<longrightarrow>
         ( sep2 v u ) \<le> (sqr e) * sep2 y x )" using d by force
      hence "(definedAt g y) \<and> (\<forall> u v . (f y u \<and> (asFunc A) y v) \<longrightarrow>
         ( sep2 v u ) \<le> (sqr e) * sep2 y x )" using g by force
      hence "(definedAt g y) \<and> (\<forall> u v . (g y u \<and> (asFunc A0) y v) \<longrightarrow>
         ( sep2 v u ) \<le> (sqr e) * sep2 y x )" 
        using g A0 assms(1) lemBallTranslation by force
    }
    hence "\<exists>d>0. \<forall>y . (y within d of x) \<longrightarrow> 
             (definedAt g y) \<and> (\<forall> u v . (g y u \<and> (asFunc A0) y v) \<longrightarrow>
                   ( sep2 v u ) \<le> (sqr e) * sep2 y x )"
      using d by force
  }
  hence rtp3d2: "\<forall>e>0. \<exists>d > 0. \<forall>y . (y within d of x) \<longrightarrow> 
             (definedAt g y) \<and> (\<forall> u v . (g y u \<and> (asFunc A0) y v) \<longrightarrow>
                   ( sep2 v u ) \<le> (sqr e) * sep2 y x )"
    by auto
  hence rtp3d: "diffApprox (asFunc A0) g x" using rtp3d1 by auto

  hence rtp3: "affineApprox A0 g x" using rtp3a rtp3b rtp3c rtp3d by auto

(*  Needs to know that T is properly defined, hence inclusion of mkT *)
  thus ?thesis using g A0 mkT by best

qed


(* Local identities are globally the identity *)
lemma lemAffineIdentity:
  assumes "affine A"
and       "e > 0"
and       "\<forall> y . (y within e of x) \<longrightarrow> (A y = y)"
shows     "A = id"
proof -

  obtain T L where TL: "translation T \<and> linear L \<and> A = T\<circ>L" using assms(1) by auto

  have "x within e of x" using assms(2) by auto
  hence xfixed: "A x = x" using assms(3) by auto

  { fix p
    define d where d: "d = (p \<ominus> x)"
    then obtain a where a: "(a > 0) \<and> (norm2 (a\<otimes>d) < sqr e)"
      using assms(2) lemSmallPoints[of "e" "d"] by auto

    define p' where p': "p' = ((a\<otimes>d)\<oplus>x)"
    hence p'fixed: "A p' = p'" using a assms(3) lemSep2Symmetry by auto

    have p'x: "(p' \<ominus> x) = (a \<otimes> (p \<ominus> x))" using p' d by auto
    hence "((1/a)\<otimes>(p'\<ominus>x)) = (p\<ominus>x)" using a lemScaleAssoc[of "1/a" "a" "p\<ominus>x"] by auto
    hence p: "p = (((1/a)\<otimes>(p'\<ominus>x)) \<oplus> x)" by auto

    hence "L p =  L (((1/a)\<otimes>(p'\<ominus>x)) \<oplus> x)" by auto
    also have "... = ((L ((1/a)\<otimes>(p'\<ominus>x)))  \<oplus> (L x))" using TL by blast
    also have "... = ((L x) \<oplus> (L ((1/a)\<otimes>(p'\<ominus>x))))" using add_commute by simp
    finally have "A p = ((A x) \<oplus> (L ((1/a)\<otimes>(p'\<ominus>x))))"
      using TL lemTranslationSum by auto

    hence 1: "A p = (x \<oplus> (L ((1/a)\<otimes>(p'\<ominus>x))))" using xfixed by auto

    have "(L ((1/a)\<otimes>(p'\<ominus>x))) = ((1/a) \<otimes> (L (p'\<ominus>x)))" using TL by blast
    also have "... = ((1/a) \<otimes> ( (L p') \<ominus> (L x) ))" using TL by auto
    also have "... = ((1/a) \<otimes> ( (A p') \<ominus> (A x) ))" using TL by auto
    also have "... = ((1/a) \<otimes> (p' \<ominus> x))" using p'fixed xfixed by auto
    finally have "(L ((1/a)\<otimes>(p'\<ominus>x))) = (p\<ominus>x)" using p by auto

    hence "A p = (x \<oplus> (p \<ominus> x))" using 1 by auto
    hence "A p = p" using add_diff_eq by auto
  }
  thus ?thesis by auto
qed



end (* of class Affine *)


end (* of theory Affine *)
