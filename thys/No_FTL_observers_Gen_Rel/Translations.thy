(*
   Mike Stannett
   Feb 2023
*)

section \<open> Translations \<close>

text \<open>This theory describes translation maps. \<close>


theory Translations
  imports Functions
begin

class Translations = Functions
begin

(*
  These functions are all single-valued, so we define them
  as having type ('a Point \<Rightarrow> 'a Point). We can use the
  asFunc function to convert them to relational form
  where necessary.
*)

abbreviation mkTranslation :: "'a Point \<Rightarrow> ('a Point \<Rightarrow> 'a Point)"
  where "(mkTranslation t) \<equiv> (\<lambda> p . (p \<oplus> t))"


abbreviation translation :: "('a Point \<Rightarrow> 'a Point) \<Rightarrow> bool" 
  where "translation T \<equiv> \<exists> q . \<forall> p . ((T p) = (p \<oplus> q))"



(* ****************************************************************** *)
(* LEMMAS *)

lemma lemMkTrans: "\<forall> t . translation (mkTranslation t)"
  by auto


lemma lemInverseTranslation:
  assumes "(T = mkTranslation t) \<and> (T' = mkTranslation (origin \<ominus> t))"
  shows     "(T' \<circ> T = id) \<and> (T \<circ> T' = id)"
using assms by auto


lemma lemTranslationSum:
  assumes "translation T"
  shows   "T (u \<oplus> v) = ((T u) \<oplus> v)"
proof -
  obtain t where t: "\<forall> x. T x = (x \<oplus> t)" using assms(1) by auto
  thus ?thesis using add_commute add_assoc t by auto
qed


lemma lemIdIsTranslation: "translation id"
proof -
  have "\<forall> p . (id p) = (p \<oplus> origin)" by simp
  thus ?thesis by blast
qed



lemma lemTranslationCancel:
  assumes "translation T"
  shows   "((T p) \<ominus> (T q)) = (p \<ominus> q)"
proof -
  obtain t where t: "\<forall> x. T x = (x \<oplus> t)" using assms(1) by auto
  hence "((p \<oplus> t) \<ominus> (q \<oplus> t)) = (p \<ominus> q)" by simp
  thus ?thesis using t by auto
qed  


lemma lemTranslationSwap:
  assumes "translation T"
  shows   "(p \<oplus> (T q)) = ((T p) \<oplus> q)"
proof -
  obtain t where t: "\<forall> x . T x = (x \<oplus> t)" using assms(1) by auto
  thus ?thesis using add_commute add_assoc by simp
qed


(* TRANSLATION LEMMAS *)

lemma lemTranslationPreservesSep2:
  assumes "translation T"
  shows "sep2 p q = sep2 (T p) (T q)"
proof -
  obtain t where "\<forall>x. T x = (x \<oplus> t)" using assms(1) by auto
  thus ?thesis by force
qed



lemma lemTranslationInjective:
  assumes "translation T"
  shows   "injective (asFunc T)"
proof -
  obtain t where t: "\<forall> x . T x = (x \<oplus> t)" using assms(1) by auto
  define Tinv where Tinv: "Tinv = mkTranslation (origin \<ominus> t)"
  { fix x y
    assume "T x = T y"
    hence "(Tinv \<circ> T) x = (Tinv \<circ> T) y" by auto
    hence "x = y" using Tinv t by auto
  }
  thus ?thesis by auto
qed


lemma lemTranslationSurjective:
  assumes "translation T"
  shows   "surjective (asFunc T)"
proof -
  obtain t where t: "\<forall> x . T x = (x \<oplus> t)" using assms(1) by auto
  hence mkT: "T = mkTranslation t" by auto
  define Tinv where Tinv: "Tinv = mkTranslation (origin \<ominus> t)"
  hence "\<forall>y . y = T (Tinv y)" using mkT lemInverseTranslation by auto
  thus ?thesis by auto
qed


lemma lemTranslationTotalFunction:
  assumes "translation T"
  shows   "isTotalFunction (asFunc T)"
by simp


lemma lemTranslationOfLine: 
  assumes "translation T"
  shows   "(applyToSet (asFunc T) (line B D)) = line (T B) D"
proof -
  define l where l: "l = line B D"
  { fix q'
    { assume "q' \<in> (applyToSet (asFunc T) l)"
      then obtain q where q: "q \<in> l \<and> (asFunc T) q q'" by auto
      then obtain \<alpha> where \<alpha>: "q = (B \<oplus> (\<alpha>\<otimes>D))" using l by auto
      have "q' = T q" using q by auto
      also have "\<dots> = ((T B) \<oplus> (\<alpha>\<otimes>D))" using \<alpha> assms lemTranslationSum by blast
      finally have "q' \<in> line (T B) D" by auto
    }
    hence l2r: "q' \<in> (applyToSet (asFunc T) l) \<longrightarrow> q' \<in> line (T B) D" by auto
    { assume "q' \<in> line (T B) D"
      then obtain \<alpha> where \<alpha>: "q' = ((T B) \<oplus> (\<alpha>\<otimes>D))" by auto
      hence "q' = T (B \<oplus> (\<alpha>\<otimes>D))" using assms lemTranslationSum[of "T" "B" "(\<alpha>\<otimes>D)"] by auto
      moreover have "(B \<oplus> (\<alpha>\<otimes>D)) \<in> l" using l by auto
      ultimately have "q' \<in> (applyToSet (asFunc T) l)" by auto
    }
    hence "q' \<in> line (T B) D \<longleftrightarrow> q' \<in> (applyToSet (asFunc T) l)" using l2r by auto
  }
  thus ?thesis using l by auto
qed


lemma lemOnLineTranslation:
  assumes "(translation T) \<and> (onLine p l)"
shows     "onLine (T p) (applyToSet (asFunc T) l)"
proof -
  obtain B D where BD: "l = line B D" using assms by auto
  hence "(applyToSet (asFunc T) l) = line (T B) D" using assms lemTranslationOfLine by auto
  moreover have "T p \<in> (applyToSet (asFunc T) l)" using assms by auto
  ultimately show ?thesis by blast
qed



lemma lemLineJoiningTranslation:
  assumes "translation T"
  shows   "applyToSet (asFunc T) (lineJoining p q) = lineJoining (T p) (T q)"
proof -
  define D where D: "D = (q\<ominus>p)"
  hence "lineJoining p q = line p D" by auto
  hence "applyToSet (asFunc T) (lineJoining p q) =  line (T p) D" 
    using assms lemTranslationOfLine by auto
  moreover have "((T q) \<ominus> (T p)) = (q\<ominus>p)" using assms lemTranslationCancel by auto
  ultimately show ?thesis using D by auto
qed





lemma lemBallTranslation:
  assumes "translation T"
and       "x within e of y"
  shows   "(T x) within e of (T y)"
proof -
  have "sep2 (T x) (T y) = sep2 x y" 
    using assms(1) lemTranslationPreservesSep2[of "T"] by auto
  thus ?thesis using assms(2) by auto
qed


lemma lemBallTranslationWithBoundary:
  assumes "translation T"
and       "sep2 x y \<le> sqr e"
  shows   "sep2 (T x) (T y) \<le> sqr e"
proof -
  have "sep2 (T x) (T y) = sep2 x y" 
    using assms(1) lemTranslationPreservesSep2[of "T" "x" "y"] by simp
  thus ?thesis using assms(2) by auto
qed


lemma lemTranslationIsCts:
  assumes "translation T"
  shows "cts (asFunc T) x"
proof -
  { fix x'
    assume x': "x' = T x"

    { fix e
      assume epos: "e > 0"
      { fix p'
        assume p': "p' \<in> applyToSet (asFunc T) (ball x e)"
        then obtain p where p: "(p \<in> ball x e) \<and> p' = T p" by auto
        hence "sep2 p x < sqr e" using lemSep2Symmetry by force
        hence "sep2 p' x' < sqr e" using assms(1) p x' lemBallTranslation by auto
      }
      hence "applyToSet (asFunc T) (ball x e) \<subseteq> ball x' e"
        using lemSep2Symmetry by force
      hence "\<exists>d>0. applyToSet (asFunc T) (ball x d) \<subseteq> ball x' e"
        using epos lemSep2Symmetry by auto
    }
    hence "\<forall>e>0. \<exists>d>0. applyToSet (asFunc T) (ball x d) \<subseteq> ball x' e"
      by auto
  }
  thus ?thesis by auto
qed



lemma lemAccPointTranslation:
  assumes "translation T"
and       "accPoint x s"
shows     "accPoint (T x) (applyToSet (asFunc T) s)"
proof -
  { fix e
    assume "e > 0"
    then obtain q where q: "q \<in> s \<and> (x \<noteq> q) \<and> (inBall q e x)" 
      using assms(2) by auto

    have acc1: "q \<in> s" using q by auto
    have acc2: "x \<noteq> q" using q by auto
    have acc3: "inBall q e x" using q by auto

    define q' where q': "q' = T q"

    have rtp1: "q' \<in> applyToSet (asFunc T) s" using q' acc1 by auto
    have rtp2: "T x \<noteq> q'" using assms(1) acc2 lemTranslationInjective[of "T"] q' by force
    have rtp3: "inBall q' e (T x)" 
      using assms(1) acc3 q' lemBallTranslation[of "T" "q" "x" "e"] by auto

    hence "\<exists> q' . (q' \<in> applyToSet (asFunc T) s) \<and> (T x \<noteq> q')
                    \<and> (inBall q' e (T x))"
      using rtp1 rtp2 by auto
  }
  thus ?thesis by auto
qed


lemma lemInverseOfTransIsTrans:
  assumes "translation T"
and       "T' = invFunc (asFunc T)"
  shows   "translation (toFunc T')"
proof -
  obtain t where t: "\<forall>p . T p = (p \<oplus> t)" using assms(1) by auto
  hence mkT: "T = mkTranslation t" by auto
  define T1 where T1: "T1 = mkTranslation (origin \<ominus> t)"
  hence transT1: "translation T1" using lemMkTrans by blast

  have TT1: "(T \<circ> T1 = id) \<and> (T1 \<circ> T = id)" using t T1 lemInverseTranslation by auto

  { fix p r
    { assume "invFunc (asFunc T) p r"
      hence "T r = p" by simp
      hence "T1 p = (T1\<circ>T) r" by auto
      hence "T1 p = r" using TT1 by simp
    }
    hence l2r: "invFunc (asFunc T) p r \<longrightarrow> (asFunc T1) p r" by auto
    { assume "(asFunc T1) p r"
      hence T'p: "T1 p = r" by simp
      have "(T \<circ> T1) p = T r" using T'p by auto
      hence "p = T r" using TT1 by auto
    }
    hence "(asFunc T1) p r \<longleftrightarrow> invFunc (asFunc T) p r" using l2r by force
  }
  hence "(asFunc T1) = T'" using assms(2) by fastforce

  hence "toFunc T' = toFunc (asFunc T1)" using assms(2) by fastforce
  hence "toFunc T' = T1" by fastforce
  thus ?thesis using transT1 by auto
qed



lemma lemInverseTrans:
assumes "translation T"
shows   "\<exists>T' . (translation T') \<and> (\<forall> p q . T p = q \<longleftrightarrow> T' q = p)"
proof -
  obtain t where t: "\<forall>p . T p = (p \<oplus> t)" using assms by auto
  hence mkT: "T = mkTranslation t" by auto
  define T' where T': "T' = mkTranslation (origin \<ominus> t)"
  hence trans': "translation T'" using lemMkTrans by blast

  have TT': "(T'\<circ>T = id) \<and> (T\<circ>T' = id)" using mkT T' lemInverseTranslation by auto

  { fix p q
    { assume "T p = q"
      hence "T' q = (T' \<circ> T) p" by auto
      hence "T' q = p" using TT' by auto
    }
    hence l2r: "T p = q \<longrightarrow> T' q = p" by auto
    { assume "T' q = p"
      hence "T p = (T\<circ>T') q" by auto
      hence "T p = q" using TT' by auto
    }
    hence "T' q = p \<longleftrightarrow> T p = q" using l2r by blast
  }
  thus ?thesis using trans' by blast
qed
    



end (* of class Translations *)


end (* of theory Translation *)
