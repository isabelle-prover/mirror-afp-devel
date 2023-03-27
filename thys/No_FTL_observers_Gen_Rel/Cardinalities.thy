(*
  Cardinalities.thy
  Author: Mike Stannett
  Date: Feb 2023
*)
section \<open> Cardinalities \<close>

text \<open> For our purposes the only relevant cardinalities are 0, 1, 2 and more-than-2 
(a proxy for "infinite"). We will use these cardinalities when looking at how
lines intersect cones, using the size of the intersection set to characterise
whether points are inside, on or outside of lightcones.\<close>



theory Cardinalities
  imports Functions
begin


class Cardinalities = Functions
begin


lemma lemInjectiveValueUnique:
  assumes "injective f"
and       "isFunction f"
and       "f x y"
shows     "{ q. f x q } = { y }"
  using assms(2) assms(3) by force



lemma lemBijectionOnTwo:
  assumes "bijective f"
and       "isFunction f"
and       "s \<subseteq> domain f"
and       "card s = 2"
shows     "card (applyToSet f s) = 2"
proof -
  obtain x y where xy: "s = {x,y} \<and> x \<noteq> y" using assms(4)
    by (meson card_2_iff)
  obtain fx where fx: "f x fx" using xy assms(1) assms(3) by blast
  obtain fy where fy: "f y fy" using xy assms(1) assms(3) by blast
  have "applyToSet f s = { q . \<exists> p \<in> s . f p q }" by simp
  moreover have "\<dots> = { q. f x q \<or> f y q }" using xy by auto
  moreover have "\<dots> = { q. f x q } \<union> { q. f y q }" by auto
  ultimately have "applyToSet f s = { fx } \<union> { fy }" 
    using fx fy  assms(1) assms(2) lemInjectiveValueUnique by force
  moreover have "fx \<noteq> fy" using fx fy assms(1) xy by blast
  thus ?thesis using calculation by force
qed


lemma lemElementsOfSet2:
  assumes "card S = 2"
  shows "\<exists> p q . (p \<noteq> q) \<and> p \<in> S \<and> q \<in> S"
  by (meson assms card_2_iff')


lemma lemThirdElementOfSet2:
  assumes "(p \<noteq> q) \<and> p \<in> S \<and> q \<in> S \<and> (card S = 2)"
and       "r \<in> S"
shows     "p = r \<or> q = r"
proof -
  have "card S = 2" using assms(1) by auto
  then obtain x y where xy: "(x \<in> S) \<and> (y \<in> S) \<and> (x \<noteq> y) \<and> (\<forall>z\<in>S. z = x \<or> z = y)" 
    using card_2_iff'[of "S"] by auto
  have p: "p = x \<or> p = y" using xy assms(1) by auto
  have q: "q = x \<or> q = y" using xy assms(1) by auto
  hence pq: "(p = x \<and> q = y) \<or> (p = y \<and> q = x)" using assms(1) p by blast
  moreover have "r = x \<or> r = y" using xy assms(2) by auto
  ultimately show ?thesis by auto
qed



lemma lemSmallCardUnderInvertible:
  assumes "invertible f"
and       "0 < card S \<le> 2"
shows "card S = card (applyToSet (asFunc f) S)"
proof -
  have cases: "card S = 1 \<or> card S = 2" using assms(2) by auto

  have case1: "card S = 1 \<longrightarrow> ?thesis"
  proof -
    { assume card1: "card S = 1"
      hence "\<exists> a . S = {a}" by (meson card_1_singletonE)
      then obtain a where a: "S = {a}" by blast
      define b where b: "b = f a"
      hence "applyToSet (asFunc f) S = { b }" 
      proof -
        have "{b} \<subseteq> applyToSet (asFunc f) S" using a b by auto
        moreover have "applyToSet (asFunc f) S \<subseteq> {b}"
        proof -
          { fix c assume c: "c \<in> applyToSet (asFunc f) S"
            hence "c \<in> { c . \<exists> a' \<in> S . (asFunc f) a' c }" by auto
            then obtain a' where a': "a' \<in> S \<and> (asFunc f) a' c" by blast
            hence "a' = a \<and> f a = c" using a by auto
            hence "c \<in> {b}" using b by auto
          }
          thus ?thesis by blast
        qed
        ultimately show ?thesis by blast
      qed
      hence "\<exists> b . applyToSet (asFunc f) S = { b }" by blast
      hence "card (applyToSet (asFunc f) S) = 1" by auto
    }
    thus ?thesis by auto
  qed

  have case2: "card S = 2 \<longrightarrow> ?thesis"
  proof -
    { assume card2: "card S = 2"
      hence "\<exists> a u . a\<noteq>u \<and> S = {a, u}" by (meson card_2_iff)
      then obtain a u where au: "a\<noteq>u \<and> S = {a, u}" by blast
      define b where b: "b = f a"
      define v where v: "v = f u"
      hence "applyToSet (asFunc f) S = { b, v }" 
      proof -
        have "{b, v} \<subseteq> applyToSet (asFunc f) S" using au b v by auto
        moreover have "applyToSet (asFunc f) S \<subseteq> {b, v}"
        proof -
          { fix c assume c: "c \<in> applyToSet (asFunc f) S"
            hence "c \<in> { c . \<exists> a' \<in> S . (asFunc f) a' c }" by auto
            then obtain a' where a': "a' \<in> S \<and> (asFunc f) a' c" by blast
            hence "(a' = a  \<and> f a = c) \<or> (a' = u \<and> f u = c)" using au by auto
            hence "c \<in> {b, v}" using b v by auto
          }
          thus ?thesis by blast
        qed
        ultimately show ?thesis by blast
      qed
      moreover have "b \<noteq> v" 
      proof -
        { assume "b = v"
          hence "f a = f u" using b v by simp
          hence "a = u" using assms(1) by blast
          hence "False" using au by auto
        }
        thus ?thesis by auto
      qed
      ultimately have "\<exists> b v . b\<noteq>v \<and> applyToSet (asFunc f) S = { b, v }" by blast

      hence "card (applyToSet (asFunc f) S) = 2"  using card_2_iff by auto
    }
    thus ?thesis by auto
  qed

  thus ?thesis using cases case1 by blast
qed


lemma lemCardOfLineIsBig:
  assumes "x \<noteq> p"
and       "onLine x l \<and> onLine p l"
shows     "\<exists> p1 p2 p3 . (onLine p1 l \<and> onLine p2 l \<and> onLine p3 l)
                        \<and> (p1\<noteq>p2 \<and> p2\<noteq>p3 \<and> p3\<noteq>p1)"
proof -
  obtain b d where bd: "l = line b d" using assms(2) by blast
  hence dnot0: "d \<noteq> origin" using assms by auto
  have lpd: "l = line p d" using lemSameLine[of "p" "b" "d"] bd assms(2) by auto

  define p1 where p1: "p1 = (p \<oplus> (1 \<otimes> d))"
  define p2 where p2: "p2 = (p \<oplus> (2 \<otimes> d))"
  define p3 where p3: "p3 = (p \<oplus> (3 \<otimes> d))"

  have onl: "onLine p1 l \<and> onLine p2 l \<and> onLine p3 l" using lpd p1 p2 p3 by auto

  have psdiff: "p1 \<noteq> p2 \<and> p2 \<noteq> p3 \<and> p3 \<noteq> p1"
  proof -
    have "p1 \<noteq> p2" using p1 p2 dnot0 by auto
    moreover have "p2 \<noteq> p3" using p2 p3 dnot0 by auto
    moreover have "p3 \<noteq> p1" using p3 p1 dnot0 by auto
    ultimately show ?thesis by blast
  qed

  hence "(onLine p1 l \<and> onLine p2 l \<and> onLine p3 l)\<and>(p1\<noteq>p2 \<and> p2\<noteq>p3 \<and> p3\<noteq>p1)"
    using onl by blast
  thus ?thesis using p1 p2 p3 by meson
qed


end (* of class Cardinalities *)
end (* of theory Cardinalities *)
