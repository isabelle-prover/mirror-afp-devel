(*  Title:       FreeCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter FreeCategory

theory FreeCategory
imports Category ConcreteCategory
begin

  text\<open>
    This theory defines locales for constructing the free category generated by
    a graph, as well as some special cases, including the discrete category generated
    by a set of objects, the ``quiver'' generated by a set of arrows, and a ``parallel pair''
    of arrows, which is the diagram shape required for equalizers.
    Other diagram shapes can be constructed in a similar fashion.
\<close>

  section Graphs

  text\<open>
    The following locale gives a definition of graphs in a traditional style.
\<close>

  locale graph =
  fixes Obj :: "'obj set"
  and Arr :: "'arr set"
  and Dom :: "'arr \<Rightarrow> 'obj"
  and Cod :: "'arr \<Rightarrow> 'obj"
  assumes dom_is_obj: "x \<in> Arr \<Longrightarrow> Dom x \<in> Obj"
  and cod_is_obj: "x \<in> Arr \<Longrightarrow> Cod x \<in> Obj"
  begin

    text\<open>
      The list of arrows @{term p} forms a path from object @{term x} to object @{term y}
      if the domains and codomains of the arrows match up in the expected way.
\<close>

    definition path
    where "path x y p \<equiv> (p = [] \<and> x = y \<and> x \<in> Obj) \<or>
                        (p \<noteq> [] \<and> x = Dom (hd p) \<and> y = Cod (last p) \<and>
                        (\<forall>n. n \<ge> 0 \<and> n < length p \<longrightarrow> nth p n \<in> Arr) \<and>
                        (\<forall>n. n \<ge> 0 \<and> n < (length p)-1 \<longrightarrow> Cod (nth p n) = Dom (nth p (n+1))))"

    lemma path_Obj:
    assumes "x \<in> Obj"
    shows "path x x []"
      using assms path_def by simp

    lemma path_single_Arr:
    assumes "x \<in> Arr"
    shows "path (Dom x) (Cod x) [x]"
      using assms path_def by simp

    lemma path_concat:
    assumes "path x y p" and "path y z q"
    shows "path x z (p @ q)"
    proof -
      have "p = [] \<or> q = [] \<Longrightarrow> ?thesis"
        using assms path_def by auto
      moreover have "p \<noteq> [] \<and> q \<noteq> [] \<Longrightarrow> ?thesis"
      proof -
        assume pq: "p \<noteq> [] \<and> q \<noteq> []"
        have Cod_last: "Cod (last p) = Cod (nth (p @ q) ((length p)-1))"
          using assms pq by (simp add: last_conv_nth nth_append)
        moreover have Dom_hd: "Dom (hd q) = Dom (nth (p @ q) (length p))"
          using assms pq by (simp add: hd_conv_nth less_not_refl2 nth_append)
        show ?thesis
        proof -
          have 1: "\<And>n. n \<ge> 0 \<and> n < length (p @ q) \<Longrightarrow> nth (p @ q) n \<in> Arr"
          proof -
            fix n
            assume n: "n \<ge> 0 \<and> n < length (p @ q)"
            have "(n \<ge> 0 \<and> n < length p) \<or> (n \<ge> length p \<and> n < length (p @ q))"
              using n by auto
            thus "nth (p @ q) n \<in> Arr"
              using assms pq nth_append path_def le_add_diff_inverse length_append
                    less_eq_nat.simps(1) nat_add_left_cancel_less
              by metis
          qed
          have 2: "\<And>n. n \<ge> 0 \<and> n < length (p @ q) - 1 \<Longrightarrow>
                                    Cod (nth (p @ q) n) = Dom (nth (p @ q) (n+1))"
          proof -
            fix n
            assume n: "n \<ge> 0 \<and> n < length (p @ q) - 1"
            have 1: "(n \<ge> 0 \<and> n < (length p) - 1) \<or> (n \<ge> length p \<and> n < length (p @ q) - 1)
                       \<or> n = (length p) - 1"
              using n by auto
            thus "Cod (nth (p @ q) n) = Dom (nth (p @ q) (n+1))"
            proof -
              have "n \<ge> 0 \<and> n < (length p) - 1 \<Longrightarrow> ?thesis"
                using assms pq nth_append path_def by (metis add_lessD1 less_diff_conv)
              moreover have "n = (length p) - 1 \<Longrightarrow> ?thesis"
                using assms pq nth_append path_def Dom_hd Cod_last by simp
              moreover have "n \<ge> length p \<and> n < length (p @ q) - 1 \<Longrightarrow> ?thesis"
              proof -
                assume 1: "n \<ge> length p \<and> n < length (p @ q) - 1"
                have "Cod (nth (p @ q) n) = Cod (nth q (n - length p))"
                  using 1 nth_append leD by metis
                also have "... = Dom (nth q (n - length p + 1))"
                  using 1 assms(2) path_def by auto
                also have "... = Dom (nth (p @ q) (n + 1))"
                  using 1 nth_append
                  by (metis Nat.add_diff_assoc2 ex_least_nat_le le_0_eq le_add1 le_neq_implies_less
                            le_refl le_trans length_0_conv pq)
                finally show "Cod (nth (p @ q) n) = Dom (nth (p @ q) (n + 1))" by auto
              qed
              ultimately show ?thesis using 1 by auto
            qed
          qed
          show ?thesis
            unfolding path_def using assms pq path_def hd_append2 Cod_last Dom_hd 1 2
            by simp
        qed
      qed
      ultimately show ?thesis by auto
    qed

  end

  section "Free Categories"

  text\<open>
    The free category generated by a graph has as its arrows all triples @{term "MkArr x y p"},
    where @{term x} and @{term y} are objects and @{term p} is a path from @{term x} to @{term y}.
    We construct it here an instance of the general construction given by the
    @{locale concrete_category} locale.
\<close>

  locale free_category =
    G: graph Obj Arr D C
  for Obj :: "'obj set"
  and Arr :: "'arr set"
  and D :: "'arr \<Rightarrow> 'obj"
  and C :: "'arr \<Rightarrow> 'obj"
  begin

    type_synonym ('o, 'a) arr = "('o, 'a list) concrete_category.arr"

    sublocale concrete_category \<open>Obj :: 'obj set\<close> \<open>\<lambda>x y. Collect (G.path x y)\<close>
      \<open>\<lambda>_. []\<close> \<open>\<lambda>_ _ _ g f. f @ g\<close>
      using G.path_Obj G.path_concat
      by (unfold_locales, simp_all)

    abbreviation comp      (infixr \<open>\<cdot>\<close> 55)
    where "comp \<equiv> COMP"
    notation in_hom     (\<open>\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>\<close>)

    abbreviation Path
    where "Path \<equiv> Map"

    lemma arr_single [simp]:
    assumes "x \<in> Arr"
    shows "arr (MkArr (D x) (C x) [x])"
      using assms
      by (simp add: G.cod_is_obj G.dom_is_obj G.path_single_Arr)

  end

  section "Discrete Categories"

  text\<open>
    A discrete category is a category in which every arrow is an identity.
    We could construct it as the free category generated by a graph with no
    arrows, but it is simpler just to apply the @{locale concrete_category}
    construction directly.
\<close>

  locale discrete_category =
  fixes Obj :: "'obj set"
  begin

    type_synonym 'o arr = "('o, unit) concrete_category.arr"

    sublocale concrete_category \<open>Obj :: 'obj set\<close> \<open>\<lambda>x y. if x = y then {x} else {}\<close>
      \<open>\<lambda>x. x\<close> \<open>\<lambda>_ _ x _ _. x\<close>
      apply unfold_locales
          apply simp_all
        apply (metis empty_iff)
      by (metis empty_iff singletonD)

    abbreviation comp      (infixr \<open>\<cdot>\<close> 55)
    where "comp \<equiv> COMP"
    notation in_hom        (\<open>\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>\<close>)

    lemma is_discrete:
    shows "arr f \<longleftrightarrow> ide f"
      using ide_char\<^sub>C\<^sub>C arr_char by simp

    lemma arr_char:
    shows "arr f \<longleftrightarrow> Dom f \<in> Obj \<and> f = MkIde (Dom f)"
      using is_discrete
      by (metis (no_types, lifting) cod_char dom_char ide_MkIde ide_char\<^sub>C\<^sub>C ide_char')

    lemma arr_char':
    shows "arr f \<longleftrightarrow> f \<in> MkIde ` Obj"
      using arr_char image_iff by auto

    lemma dom_char:
    shows "dom f = (if arr f then f else null)"
      using dom_char is_discrete by simp

    lemma cod_char:
    shows "cod f = (if arr f then f else null)"
      using cod_char is_discrete by simp

    lemma in_hom_char:
    shows "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<longleftrightarrow> arr f \<and> f = a \<and> f = b"
      using is_discrete by auto

    lemma seq_char:
    shows "seq g f \<longleftrightarrow> arr f \<and> f = g"
      using is_discrete
      by (metis (no_types, lifting) comp_arr_dom seqE dom_char)
    
    lemma comp_char:
    shows "g \<cdot> f = (if seq g f then f else null)"
    proof -
      have "\<not> seq g f \<Longrightarrow> ?thesis"
        using comp_char by presburger
      moreover have "seq g f \<Longrightarrow> ?thesis"
        using seq_char comp_char comp_arr_ide is_discrete
        by (metis (no_types, lifting))
      ultimately show ?thesis by blast
    qed

  end

  text\<open>
    The empty category is the discrete category generated by an empty set of objects.
\<close>

  locale empty_category =
    discrete_category "{} :: unit set"
  begin

    lemma is_empty:
    shows "\<not>arr f"
      using arr_char by simp

  end

  section "Quivers"

  text\<open>
    A quiver is a two-object category whose non-identity arrows all point in the
    same direction.  A quiver is specified by giving the set of these non-identity arrows.
\<close>

  locale quiver =
  fixes Arr :: "'arr set"
  begin

    type_synonym 'a arr = "(unit, 'a) concrete_category.arr"

    sublocale free_category "{False, True}" Arr "\<lambda>_. False" "\<lambda>_. True"
      by (unfold_locales, simp_all)

    notation comp                  (infixr \<open>\<cdot>\<close> 55)
    notation in_hom                (\<open>\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>\<close>)

    definition Zero
    where "Zero \<equiv> MkIde False"

    definition One
    where "One \<equiv> MkIde True"

    definition fromArr
    where "fromArr x \<equiv> if x \<in> Arr then MkArr False True [x] else null"

    definition toArr
    where "toArr f \<equiv> hd (Path f)"

    lemma ide_char:
    shows "ide f \<longleftrightarrow> f = Zero \<or> f = One"
    proof -
      have "ide f \<longleftrightarrow> f = MkIde False \<or> f = MkIde True"
        using ide_char\<^sub>C\<^sub>C concrete_category.MkIde_Dom' concrete_category_axioms by fastforce
      thus ?thesis
        using comp_def Zero_def One_def by simp
    qed

    lemma arr_char':
    shows "arr f \<longleftrightarrow> f =
           MkIde False \<or> f = MkIde True \<or> f \<in> (\<lambda>x. MkArr False True [x]) ` Arr"
    proof
      assume f: "f = MkIde False \<or> f = MkIde True \<or> f \<in> (\<lambda>x. MkArr False True [x]) ` Arr"
      show "arr f" using f by auto
      next
      assume f: "arr f"
      have "\<not>(f = MkIde False \<or> f = MkIde True) \<Longrightarrow> f \<in> (\<lambda>x. MkArr False True [x]) ` Arr"
      proof -
        assume f': "\<not>(f = MkIde False \<or> f = MkIde True)"
        have 0: "Dom f = False \<and> Cod f = True"
          using f f' arr_char G.path_def MkArr_Map by fastforce
        have 1: "f = MkArr False True (Path f)"
          using f 0 arr_char MkArr_Map by force
        moreover have "length (Path f) = 1"
        proof -
          have "length (Path f) \<noteq> 0"
            using f f' 0 arr_char G.path_def by simp
          moreover have "\<And>x y p. length p > 1 \<Longrightarrow> \<not> G.path x y p"
            using G.path_def less_diff_conv by fastforce
          ultimately show ?thesis
            using f arr_char
            by (metis less_one linorder_neqE_nat mem_Collect_eq)
        qed
        moreover have "\<And>p. length p = 1 \<longleftrightarrow> (\<exists>x. p = [x])"
          by (auto simp: length_Suc_conv)
        ultimately have "\<exists>x. x \<in> Arr \<and> Path f = [x]"
          using f G.path_def arr_char
          by (metis (no_types, lifting) Cod.simps(1) Dom.simps(1) le_eq_less_or_eq
              less_numeral_extra(1) mem_Collect_eq nth_Cons_0)
        thus "f \<in> (\<lambda>x. MkArr False True [x]) ` Arr"
          using 1 by auto
      qed
      thus "f = MkIde False \<or> f = MkIde True \<or> f \<in> (\<lambda>x. MkArr False True [x]) ` Arr"
        by auto
    qed

    lemma arr_char:
    shows "arr f \<longleftrightarrow> f = Zero \<or> f = One \<or> f \<in> fromArr ` Arr"
      using arr_char' Zero_def One_def fromArr_def by simp

    lemma dom_char:
    shows "dom f = (if arr f then
                      if f = One then One else Zero
                    else null)"
    proof -
      have "\<not> arr f \<Longrightarrow> ?thesis"
        using dom_char by simp
      moreover have "arr f \<Longrightarrow> ?thesis"
      proof -
        assume f: "arr f"
        have 1: "dom f = MkIde (Dom f)"
          using f dom_char by simp
        have "f = One \<Longrightarrow> ?thesis"
          using f 1 One_def by (metis (full_types) Dom.simps(1))
        moreover have "f = Zero \<Longrightarrow> ?thesis"
          using f 1 Zero_def by (metis (full_types) Dom.simps(1))
        moreover have "f \<in> fromArr ` Arr \<Longrightarrow> ?thesis"
          using f fromArr_def G.path_def Zero_def calculation(1) by auto
        ultimately show ?thesis
          using f arr_char by blast
      qed
      ultimately show ?thesis by blast
    qed

    lemma cod_char:
    shows "cod f = (if arr f then
                      if f = Zero then Zero else One
                    else null)"
    proof -
      have "\<not> arr f \<Longrightarrow> ?thesis"
        using cod_char by simp
      moreover have "arr f \<Longrightarrow> ?thesis"
      proof -
        assume f: "arr f"
        have 1: "cod f = MkIde (Cod f)"
          using f cod_char by simp
        have "f = One \<Longrightarrow> ?thesis"
          using f 1 One_def by (metis (full_types) Cod.simps(1) f)
        moreover have "f = Zero \<Longrightarrow> ?thesis"
          using f 1 Zero_def by (metis (full_types) Cod.simps(1) f)
        moreover have "f \<in> fromArr ` Arr \<Longrightarrow> ?thesis"
          using f fromArr_def G.path_def One_def calculation(2) by auto
        ultimately show ?thesis
          using f arr_char by blast
      qed
      ultimately show ?thesis by blast
    qed

    lemma seq_char:
    shows "seq g f \<longleftrightarrow> arr g \<and> arr f \<and> ((f = Zero \<and> g \<noteq> One) \<or> (f \<noteq> Zero \<and> g = One))"
    proof
      assume gf: "arr g \<and> arr f \<and> ((f = Zero \<and> g \<noteq> One) \<or> (f \<noteq> Zero \<and> g = One))"
      show "seq g f"
        using gf dom_char cod_char by auto
      next
      assume gf: "seq g f"
      hence 1: "arr f \<and> arr g \<and> dom g = cod f" by auto
      have "Cod f = False \<Longrightarrow> f = Zero"
        using gf 1 arr_char [of f] G.path_def Zero_def One_def cod_char Dom_cod
        by (metis (no_types, lifting) Dom.simps(1))
      moreover have "Cod f = True \<Longrightarrow> g = One"
        using gf 1 arr_char [of f] G.path_def Zero_def One_def dom_char Dom_cod
        by (metis (no_types, lifting) Dom.simps(1))
      moreover have "\<not>(f = MkIde False \<and> g = MkIde True)"
        using 1 by auto
      ultimately show "arr g \<and> arr f \<and> ((f = Zero \<and> g \<noteq> One) \<or> (f \<noteq> Zero \<and> g = One))"
        using gf arr_char One_def Zero_def by blast
    qed

    lemma not_ide_fromArr:
    shows "\<not> ide (fromArr x)"
      using fromArr_def ide_char ide_def Zero_def One_def
      by (metis Cod.simps(1) Dom.simps(1))

    lemma in_hom_char:
    shows "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<longleftrightarrow> (a = Zero \<and> b = Zero \<and> f = Zero) \<or>
                            (a = One \<and> b = One \<and> f = One) \<or>
                            (a = Zero \<and> b = One \<and> f \<in> fromArr ` Arr)"
    proof -
      have "f = Zero \<Longrightarrow> ?thesis"
        using arr_char' [of f] ide_char'
        by (metis (no_types, lifting) Zero_def category.in_homE category.in_homI
            cod_MkArr dom_MkArr imageE is_category not_ide_fromArr)
      moreover have "f = One \<Longrightarrow> ?thesis"
        using arr_char' [of f] ide_char'
        by (metis (no_types, lifting) One_def category.in_homE category.in_homI
            cod_MkArr dom_MkArr image_iff is_category not_ide_fromArr)
      moreover have "f \<in> fromArr ` Arr \<Longrightarrow> ?thesis"
      proof -
        assume f: "f \<in> fromArr ` Arr"
        have 1: "arr f" using f arr_char by simp
        moreover have "dom f = Zero \<and> cod f = One"
          using f 1 arr_char dom_char cod_char fromArr_def
          by (metis (no_types, lifting) ide_char imageE not_ide_fromArr)
        ultimately have "in_hom f Zero One" by auto
        thus "in_hom f a b \<longleftrightarrow> (a = Zero \<and> b = Zero \<and> f = Zero \<or>
                                           a = One \<and> b = One \<and> f = One \<or>
                                           a = Zero \<and> b = One \<and> f \<in> fromArr ` Arr)"
          using f ide_char by auto
      qed
      ultimately show ?thesis
        using arr_char [of f] by fast
    qed

    lemma Zero_not_eq_One [simp]:
    shows "Zero \<noteq> One"
      by (simp add: One_def Zero_def)

    lemma Zero_not_eq_fromArr [simp]:
    shows "Zero \<notin> fromArr ` Arr"
      using ide_char not_ide_fromArr
      by (metis (no_types, lifting) image_iff)

    lemma One_not_eq_fromArr [simp]:
    shows "One \<notin> fromArr ` Arr"
      using ide_char not_ide_fromArr
      by (metis (no_types, lifting) image_iff)

    lemma comp_char:
    shows "g \<cdot> f = (if seq g f then
                      if f = Zero then g else if g = One then f else null
                    else null)"
    proof -
      have "seq g f \<Longrightarrow> f = Zero \<Longrightarrow> g \<cdot> f = g"
        using seq_char comp_char [of g f] Zero_def dom_char cod_char comp_arr_dom
        by auto
      moreover have "seq g f \<Longrightarrow> g = One \<Longrightarrow> g \<cdot> f = f"
        using seq_char comp_char [of g f] One_def dom_char cod_char comp_cod_arr
        by simp
      moreover have "seq g f \<Longrightarrow> f \<noteq> Zero \<Longrightarrow> g \<noteq> One \<Longrightarrow> g \<cdot> f = null"
        using seq_char Zero_def One_def by simp
      moreover have "\<not>seq g f \<Longrightarrow> g \<cdot> f = null"
        using comp_char ext by fastforce
      ultimately show ?thesis by argo
    qed

    lemma comp_simp [simp]:
    assumes "seq g f"
    shows "f = Zero \<Longrightarrow> g \<cdot> f = g"
    and "g = One \<Longrightarrow> g \<cdot> f = f"
      using assms seq_char comp_char by metis+

    lemma arr_fromArr:
    assumes "x \<in> Arr"
    shows "arr (fromArr x)"
      using assms fromArr_def arr_char image_eqI by simp

    lemma toArr_in_Arr:
    assumes "arr f" and "\<not>ide f"
    shows "toArr f \<in> Arr"
    proof -
      have "\<And>a. a \<in> Arr \<Longrightarrow> Path (fromArr a) = [a]"
        using fromArr_def arr_char by simp
      hence "hd (Path f) \<in> Arr"
        using assms arr_char ide_char by auto
      thus ?thesis
        by (simp add: toArr_def)
    qed

    lemma toArr_fromArr [simp]:
    assumes "x \<in> Arr"
    shows "toArr (fromArr x) = x"
      using assms fromArr_def toArr_def
      by (simp add: toArr_def)

    lemma fromArr_toArr [simp]:
    assumes "arr f" and "\<not>ide f"
    shows "fromArr (toArr f) = f"
      using assms fromArr_def toArr_def arr_char ide_char toArr_fromArr by auto

  end

  section "Parallel Pairs"

  text\<open>
    A parallel pair is a quiver with two non-identity arrows.
    It is important in the definition of equalizers.
\<close>

  locale parallel_pair =
    quiver "{False, True} :: bool set"
  begin

    typedef arr = "UNIV :: bool quiver.arr set" ..

    definition j0
    where "j0 \<equiv> fromArr False"

    definition j1
    where "j1 \<equiv> fromArr True"

    lemma arr_char:
    shows "arr f \<longleftrightarrow> f = Zero \<or> f = One \<or> f = j0 \<or> f = j1"
      using arr_char j0_def j1_def by simp

    lemma dom_char:
    shows "dom f = (if f = j0 \<or> f = j1 then Zero else if arr f then f else null)"
      using arr_char dom_char j0_def j1_def
      by (metis ide_char not_ide_fromArr)

    lemma cod_char:
    shows "cod f = (if f = j0 \<or> f = j1 then One else if arr f then f else null)"
      using arr_char cod_char j0_def j1_def
      by (metis ide_char not_ide_fromArr)

    lemma j0_not_eq_j1 [simp]:
    shows "j0 \<noteq> j1"
      using j0_def j1_def
      by (metis insert_iff toArr_fromArr)

    lemma Zero_not_eq_j0 [simp]:
    shows "Zero \<noteq> j0"
      using Zero_def j0_def Zero_not_eq_fromArr by auto

    lemma Zero_not_eq_j1 [simp]:
    shows "Zero \<noteq> j1"
      using Zero_def j1_def Zero_not_eq_fromArr by auto

    lemma One_not_eq_j0 [simp]:
    shows "One \<noteq> j0"
      using One_def j0_def One_not_eq_fromArr by auto

    lemma One_not_eq_j1 [simp]:
    shows "One \<noteq> j1"
      using One_def j1_def One_not_eq_fromArr by auto

    lemma dom_simp [simp]:
    shows "dom Zero = Zero"
    and "dom One = One"
    and "dom j0 = Zero"
    and "dom j1 = Zero"
      using dom_char arr_char by auto

    lemma cod_simp [simp]:
    shows "cod Zero = Zero"
    and "cod One = One"
    and "cod j0 = One"
    and "cod j1 = One"
      using cod_char arr_char by auto

  end

end
