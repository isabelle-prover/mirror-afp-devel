(*  Title:       ConcreteRTSCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2024
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

theory ConcreteRTSCategory
imports Main RTSCategory
begin

  section "Concrete RTS-Categories"

  text\<open>
    If we are given a set \<open>Obj\<close> of ``objects'', a mapping \<open>Hom\<close> that assigns to every two
    objects \<open>A\<close> and \<open>B\<close> an extensional ``hom-RTS'' RTS \<open>Hom A B\<close>, a mapping \<open>Id\<close> that assigns
    to each object \<open>A\<close> an ``identity arrow'' \<open>Id A\<close> of \<open>Hom A B\<close>, and a mapping \<open>Comp\<close> that
    assigns to every three objects \<open>A\<close>, \<open>B\<close>, \<open>C\<close> a ``composition law''
    \<open>Comp A B C\<close> from \<open>Hom B C \<times> Hom A B\<close> to \<open>Hom A B\<close>, subject to suitable identity and
    associativity conditions, then we can form from this data an RTS-category whose
    underlying set of arrows is the disjoint union of the sets of arrows of the hom-RTS's.
  \<close>

  locale concrete_rts_category =
  fixes obj_type :: "'O itself"
  and arr_type :: "'A itself"
  and Obj :: "'O set"
  and Hom :: "'O \<Rightarrow> 'O \<Rightarrow> 'A resid"
  and Id :: "'O \<Rightarrow> 'A"
  and Comp :: "'O \<Rightarrow> 'O \<Rightarrow> 'O \<Rightarrow> 'A \<Rightarrow> 'A \<Rightarrow> 'A"
  assumes rts_Hom: "\<lbrakk> A \<in> Obj; B \<in> Obj \<rbrakk> \<Longrightarrow> extensional_rts (Hom A B)"
  and binary_simulation_Comp:
        "\<lbrakk> A \<in> Obj; B \<in> Obj; C \<in> Obj \<rbrakk>
            \<Longrightarrow> binary_simulation
                  (Hom B C) (Hom A B) (Hom A C) (\<lambda>(t, u). Comp A B C t u)"
  and ide_Id: "A \<in> Obj \<Longrightarrow> residuation.ide (Hom A A) (Id A)"
  and Comp_Hom_Id: "\<lbrakk> A \<in> Obj; B \<in> Obj; residuation.arr (Hom A B) t \<rbrakk>
                       \<Longrightarrow> Comp A A B t (Id A) = t"
  and Comp_Id_Hom: "\<lbrakk> A \<in> Obj; B \<in> Obj; residuation.arr (Hom A B) u \<rbrakk>
                       \<Longrightarrow> Comp A B B (Id B) u = u"
  and Comp_assoc: "\<lbrakk> A \<in> Obj; B \<in> Obj; C \<in> Obj; D \<in> Obj;
                     residuation.arr (Hom C D) t; residuation.arr (Hom B C) u;
                     residuation.arr (Hom A B) v \<rbrakk> \<Longrightarrow>
                      Comp A B D (Comp B C D t u) v =
                      Comp A C D t (Comp A B C u v)"
  begin

    datatype ('o, 'a) arr =
      Null
    | MkArr 'o 'o 'a

    fun Dom :: "('O, 'A) arr \<Rightarrow> 'O"
    where "Dom (MkArr a _ _) = a"
        | "Dom _ = undefined"

    fun Cod :: "('O, 'A) arr \<Rightarrow> 'O"
    where "Cod (MkArr _ b _) = b"
        | "Cod _ = undefined"

    fun Trn :: "('O, 'A) arr \<Rightarrow> 'A"
    where "Trn (MkArr _ _ t) = t"
        | "Trn _ = undefined"

    abbreviation Arr :: "('O, 'A) arr \<Rightarrow> bool"
    where "Arr \<equiv> \<lambda>t. t \<noteq> Null \<and> Dom t \<in> Obj \<and> Cod t \<in> Obj \<and>
                     residuation.arr (Hom (Dom t) (Cod t)) (Trn t)"

    abbreviation Ide :: "('O, 'A) arr \<Rightarrow> bool"
    where "Ide \<equiv> \<lambda>t. t \<noteq> Null \<and> Dom t \<in> Obj \<and> Cod t \<in> Obj \<and>
                     residuation.ide (Hom (Dom t) (Cod t)) (Trn t)"

    abbreviation Con :: "('O, 'A) arr \<Rightarrow> ('O, 'A) arr \<Rightarrow> bool"
    where "Con t u \<equiv> Arr t \<and> Arr u \<and> Dom t = Dom u \<and> Cod t = Cod u \<and>
                     residuation.con (Hom (Dom t) (Cod t)) (Trn t) (Trn u)"

    fun resid  (infix \<open>\\<close> 70)
    where "resid Null u = Null"
        | "resid t Null = Null"
        | "resid t u =
           (if Con t u
            then MkArr (Dom t) (Cod t) (Hom (Dom t) (Cod t) (Trn t) (Trn u))
            else Null)"

    sublocale V: ResiduatedTransitionSystem.partial_magma resid
      apply unfold_locales
      by (metis Trn.cases resid.simps(1-2))

    lemma null_char:
    shows "V.null = Null"
      by (metis V.null_is_zero(2) resid.simps(1))

    sublocale V: residuation resid
    proof
      fix t u :: "('O, 'A) arr"
      assume tu: "t \\ u \<noteq> V.null"
      interpret hom: extensional_rts \<open>Hom (Dom t) (Cod t)\<close>
        using tu null_char rts_Hom
        by (metis arr.exhaust V.null_is_zero(2) resid.simps(1,3))
      show "t \\ u \<noteq> V.null \<Longrightarrow> u \\ t \<noteq> V.null"
        using null_char hom.con_sym
        apply (cases t; cases u)
           apply auto[3]
        by (metis arr.simps(2) resid.simps(3))
      show "(t \\ u) \\ (t \\ u) \<noteq> V.null"
        using tu null_char hom.arr_resid hom.con_arr_self
        apply (cases "t \\ u")
         apply force
        apply (cases t; cases u)
           apply auto[3]
        by (metis Cod.simps(1) Dom.simps(1) Trn.simps(1)
            arr.simps(2) resid.simps(3))
      next
      fix t u v :: "('O, 'A) arr"
      assume tuv: "(v \\ t) \\ (u \\ t) \<noteq> V.null"
      have tu: "Con t u"
        using tuv null_char V.null_is_zero(2) resid.simps(3)
        apply (cases t; cases u; cases v)
               apply auto[7]
        by (metis extensional_rts_def residuation.con_sym
            rts_Hom rts_def)
      have tv: "Con t v"
        using tu tuv null_char resid.simps(1,3)
        apply (cases t; cases u; cases v)
               apply auto[7]
        by (metis extensional_rts_def residuation.con_sym
            rts_Hom rts_def)
      interpret hom: extensional_rts \<open>Hom (Dom t) (Cod t)\<close>
        using tu null_char rts_Hom by metis
      have uv: "Con u v"
        using tu tv tuv null_char hom.con_sym
              resid.simps(1,3) rts_Hom
        apply (cases t; cases u; cases v)
               apply auto[7]
        apply (intro conjI)
                  apply auto[10]
        by auto (metis Cod.simps(1) Dom.simps(1) hom.resid_reflects_con)
      interpret hom: extensional_rts \<open>Hom (Dom t) (Cod t)\<close>
        using tu null_char rts_Hom by blast
      show "(v \\ t) \\ (u \\ t) = (v \\ u) \\ (t \\ u)"
        using tu tv uv null_char hom.arr_resid_iff_con
              hom.con_sym hom.cube
        apply (cases t; cases u; cases v)
        by auto metis+
    qed

    notation V.con  (infix \<open>\<frown>\<close> 50)

    lemma con_char:
    shows "t \<frown> u \<longleftrightarrow> Con t u"
    proof
      show "t \<frown> u \<Longrightarrow> Con t u"
        using V.con_def V.not_con_null(2) null_char
        apply (cases t; cases u)
           apply auto[3]
        by fastforce
      show "Con t u \<Longrightarrow> t \<frown> u"
        using null_char
        by (cases t; cases u) auto
    qed

    lemma arr_char:
    shows "V.arr t \<longleftrightarrow> Arr t"
      by (metis V.arr_def con_char extensional_rts_def
          residuation.arr_def rts_Hom rts_def)

    lemma arrI [intro]:
    assumes "t \<noteq> V.null" and "Dom t \<in> Obj" and "Cod t \<in> Obj"
    and "residuation.arr (Hom (Dom t) (Cod t)) (Trn t)"
    shows "V.arr t"
      using assms arr_char null_char by auto

    lemma arrE [elim]:
    assumes "V.arr t"
    and "\<lbrakk>t \<noteq> V.null; Dom t \<in> Obj; Cod t \<in> Obj;
          residuation.arr (Hom (Dom t) (Cod t)) (Trn t)\<rbrakk>
            \<Longrightarrow> T"
    shows T
      using assms arr_char by fastforce

    lemma sta_char:
    shows "V.ide t \<longleftrightarrow> Ide t"
    proof
      assume t: "V.ide t"
      interpret hom: extensional_rts \<open>Hom (Dom t) (Cod t)\<close>
        using t
        by (meson V.ide_implies_arr arrE rts_Hom)
      show "Ide t"
        using t null_char V.not_ide_null
        apply (cases t)
         apply force
        by (metis Trn.simps(1) V.ideE hom.ideI resid.simps(3))
      next
      assume t: "Ide t"
      show "V.ide t"
      proof (cases t)
        show "t = Null \<Longrightarrow> ?thesis"
          using t V.ide_def con_char by blast
        fix A B F
        assume 1: "t = MkArr A B F"
        interpret hom: extensional_rts \<open>Hom A B\<close>
          using t 1 rts_Hom by simp
        show "V.ide t"
          using t 1 V.con_def V.ide_def null_char by auto
      qed
    qed

    lemma staI [intro]:
    assumes "t \<noteq> V.null" and "Dom t \<in> Obj" and "Cod t \<in> Obj"
    and "residuation.ide (Hom (Dom t) (Cod t)) (Trn t)"
    shows "V.ide t"
      using assms sta_char null_char by auto

    lemma staE [elim]:
    assumes "V.ide t"
    and "\<lbrakk>t \<noteq> V.null; Dom t \<in> Obj; Cod t \<in> Obj;
          residuation.ide (Hom (Dom t) (Cod t)) (Trn t)\<rbrakk>
             \<Longrightarrow> T"
    shows T
      using assms sta_char by fastforce

    lemma trg_char:
    shows "V.trg t =
           (if V.arr t
            then MkArr (Dom t) (Cod t)
                   (residuation.trg (Hom (Dom t) (Cod t)) (Trn t))
            else Null)"
    proof (cases "V.arr t")
      show "\<not> V.arr t \<Longrightarrow> ?thesis"
        using V.trg_def null_char V.con_def by auto
      assume t: "V.arr t"
      interpret hom: extensional_rts \<open>Hom (Dom t) (Cod t)\<close>
        using t
        by (meson V.ide_implies_arr arrE rts_Hom)
      show ?thesis
          using t null_char
          apply (cases t)
           apply fastforce
          by (metis V.trg_def arrE hom.conI hom.ide_trg
              hom.not_ide_null hom.trg_def resid.simps(3))
    qed

    lemma con_implies_Par:
    assumes "t \<frown> u"
    shows "Dom t = Dom u" and "Cod t = Cod u"
      using assms con_char by blast+

    lemma Dom_resid [simp]:
    assumes "t \<frown> u"
    shows "Dom (t \\ u) = Dom t"
      using assms con_char
      by (cases t; cases u) auto

    lemma Cod_resid [simp]:
    assumes "t \<frown> u"
    shows "Cod (t \\ u) = Cod t"
      using assms con_char
      by (cases t; cases u) auto

    lemma Trn_resid [simp]:
    assumes "t \<frown> u"
    shows "Trn (t \\ u) = Hom (Dom t) (Cod t) (Trn t) (Trn u)"
      using assms con_char
      by (cases t; cases u) auto

    sublocale rts resid
    proof
      show "\<And>t. V.arr t \<Longrightarrow> V.ide (V.trg t)"
        by (simp add: arr_char extensional_rts.axioms(1) rts.ide_trg
            rts_Hom sta_char trg_char)
      show 1: "\<And>a t. \<lbrakk>V.ide a; t \<frown> a\<rbrakk> \<Longrightarrow> t \\ a = t"
      proof -
        fix a t
        assume a: "V.ide a"
        assume con: "t \<frown> a"
        have "t \\ a \<noteq> Null \<and> t \<noteq> Null"
          using con null_char by auto
        moreover have "Dom (t \\ a) = Dom t"
          using a con by simp
        moreover have "Cod (t \\ a) = Cod t"
          using a con by simp
        moreover have "Trn (t \\ a) = Trn t"
          using a con apply simp
          by (metis con_char extensional_rts_def sta_char rts.resid_arr_ide rts_Hom)
        ultimately show "t \\ a = t"
          by (metis Cod.elims Dom.simps(1) Trn.simps(1))
      qed
      show "\<And>a t. \<lbrakk>V.ide a; a \<frown> t\<rbrakk> \<Longrightarrow> V.ide (a \\ t)"
        using sta_char con_char
        by (metis 1 V.arr_resid V.con_arr_self V.con_sym V.cube V.ideE V.ideI)
      show "\<And>t u. t \<frown> u \<Longrightarrow> \<exists>a. V.ide a \<and> a \<frown> t \<and> a \<frown> u"
      proof -
        fix t u
        assume tu: "t \<frown> u"
        interpret hom: extensional_rts \<open>Hom (Dom t) (Cod t)\<close>
          using tu con_char arr_char [of t] rts_Hom by auto
        have 1: "hom.con (Trn t) (Trn u)"
          using tu con_char by auto
        obtain \<alpha> where \<alpha>: "hom.ide \<alpha> \<and> hom.con \<alpha> (Trn t) \<and> hom.con \<alpha> (Trn u)"
          using 1 hom.con_imp_coinitial_ax by auto
        have "V.ide (MkArr (Dom t) (Cod t) \<alpha>)"
          using tu \<alpha> V.con_implies_arr arr_char sta_char by auto
        moreover have "MkArr (Dom t) (Cod t) \<alpha> \<frown> t"
          using \<alpha> tu con_char hom.ide_implies_arr by auto
        moreover have "MkArr (Dom t) (Cod t) \<alpha> \<frown> u"
          using \<alpha> tu con_char hom.ide_implies_arr by auto
        ultimately show "\<exists>a. V.ide a \<and> a \<frown> t \<and> a \<frown> u" by blast
      qed
      show "\<And>t u v. \<lbrakk>V.ide (t \\ u); u \<frown> v\<rbrakk> \<Longrightarrow> t \\ u \<frown> v \\ u"
      proof -
        fix t u v
        assume tu: "V.ide (t \\ u)"
        assume uv: "u \<frown> v"
        have 1: "t \\ u \<noteq> V.null"
          using tu by auto
        interpret HOM: extensional_rts \<open>Hom (Dom t) (Cod t)\<close>
          using 1 con_char arr_char [of t] rts_Hom by auto
        have 2: "HOM.con (Hom (Dom t) (Cod t) (Trn t) (Trn u))
                         (Hom (Dom t) (Cod t) (Trn v) (Trn u))"
          by (metis (no_types, lifting) Cod_resid Dom_resid HOM.con_target
              Trn_resid V.conI con_char staE tu uv)
        have 3: "Con t u"
          using 1 con_char by blast
        have 4: "Con v u"
          using uv con_char V.con_sym by blast
        have 5: "t \\ u = MkArr (Dom t) (Cod t)
                                (Hom (Dom t) (Cod t) (Trn t) (Trn u))"
          using 1 3
          by (cases t; cases u) auto
        have 6: "v \\ u = MkArr (Dom v) (Cod v)
                                (Hom (Dom v) (Cod t) (Trn v) (Trn u))"
          using 3 4
          by (cases v; cases u) auto
        show "t \\ u \<frown> v \\ u"
          using 2 3 4 5 6 HOM.con_implies_arr(1-2) con_char by auto
      qed
    qed

    lemma is_rts:
    shows "rts resid"
      ..

    sublocale V: extensional_rts resid
    proof
      fix t u
      assume tu: "cong t u"
      have 1: "t \\ u \<noteq> V.null"
        using tu by auto
      interpret HOM: extensional_rts \<open>Hom (Dom t) (Cod t)\<close>
        using 1 con_char arr_char [of t] rts_Hom by auto
      have "t \<noteq> Null \<and> u \<noteq> Null"
        using tu con_char by blast
      moreover have "Dom t = Dom u"
        using tu con_char by blast
      moreover have "Cod t = Cod u"
        using tu con_char by blast
      moreover have "Trn t = Trn u"
        by (metis calculation(2-3) Cod_resid Dom_resid Trn_resid sta_char
            congE HOM.cong_char tu)
      ultimately show "t = u"
        by (metis Cod.elims Dom.simps(1) Trn.simps(1))
    qed

    lemma is_extensional_rts:
    shows "extensional_rts resid"
      ..

    lemma arr_MkArr [intro]:
    assumes "a \<in> Obj" and "b \<in> Obj"
    and "residuation.arr (Hom a b) t"
    shows "V.arr (MkArr a b t)"
      using assms arr_char by auto

    lemma arr_eqI:
    assumes "t \<noteq> Null" and "u \<noteq> Null"
    and "Dom t = Dom u" and "Cod t = Cod u" and "Trn t = Trn u"
    shows "t = u"
      using assms null_char
      by (metis Cod.elims Dom.simps(1) Trn.simps(1))

    lemma MkArr_Trn:
    assumes "V.arr t"
    shows "MkArr (Dom t) (Cod t) (Trn t) = t"
      using assms null_char V.not_arr_null
      by (intro arr_eqI) auto

    lemma src_char:
    shows "V.src t = (if V.arr t
                      then MkArr (Dom t) (Cod t)
                             (weakly_extensional_rts.src (Hom (Dom t) (Cod t)) (Trn t))
                      else Null)"
    proof (cases "V.arr t")
      show "\<not> V.arr t \<Longrightarrow> ?thesis"
        by (simp add: V.src_def null_char)
      assume t: "V.arr t"
      interpret HOM: extensional_rts \<open>Hom (Dom t) (Cod t)\<close>
        using t con_char arr_char rts_Hom by auto
      show ?thesis
        using t
        by (metis (no_types, lifting) Cod.simps(1) Dom.simps(1) HOM.src_eqI
            Trn.simps(1) V.con_arr_src(2) V.ide_src arr.simps(2) arr_eqI
            con_char staE)
    qed

    definition hcomp  (infixr \<open>\<star>\<close> 53)
    where "t \<star> u \<equiv> if V.arr t \<and> V.arr u \<and> Dom t = Cod u
                    then MkArr (Dom u) (Cod t)
                               (Comp (Dom u) (Cod u) (Cod t) (Trn t) (Trn u))
                    else V.null"

    lemma arr_hcomp\<^sub>C\<^sub>R\<^sub>C:
    assumes "V.arr t" and "V.arr u" and "Dom t = Cod u"
    shows "V.arr (t \<star> u)"
    proof -
      let ?a = "Dom u" and ?b = "Cod u" and ?c = "Cod t"
      interpret Comp: binary_simulation \<open>Hom ?b ?c\<close> \<open>Hom ?a ?b\<close> \<open>Hom ?a ?c\<close>
                        \<open>\<lambda>(t, u). Comp ?a ?b ?c t u\<close>
        using assms arr_char binary_simulation_Comp by auto
      let ?tu = "MkArr ?a ?c (Comp ?a ?b ?c (Trn t) (Trn u))"
      have "V.arr ?tu"
        using assms arr_char Comp.preserves_reflects_arr [of "(Trn t, Trn u)"]
        by simp
      thus ?thesis
        using assms hcomp_def by simp
    qed

    lemma Dom_hcomp [simp]:
    assumes "V.arr t" and "V.arr u" and "Dom t = Cod u"
    shows "Dom (t \<star> u) = Dom u"
      using assms hcomp_def by auto

    lemma Cod_hcomp [simp]:
    assumes "V.arr t" and "V.arr u" and "Dom t = Cod u"
    shows "Cod (t \<star> u) = Cod t"
      using assms hcomp_def by auto

    lemma Trn_hcomp [simp]:
    assumes "V.arr t" and "V.arr u" and "Dom t = Cod u"
    shows "Trn (t \<star> u) = Comp (Dom u) (Cod u) (Cod t) (Trn t) (Trn u)"
      using assms hcomp_def by auto

    lemma hcomp_Null [simp]:
    shows "t \<star> Null = Null" and "Null \<star> u = Null"
      using hcomp_def null_char by fastforce+

    sublocale H: Category.partial_magma hcomp
      using hcomp_def V.not_arr_null
      by unfold_locales metis

    lemma null_coincidence\<^sub>C\<^sub>R\<^sub>C [simp]:
    shows "H.null = V.null"
      using hcomp_def
      by (metis H.null_eqI V.not_arr_null)

    sublocale H: partial_composition hcomp ..

    lemma H_composable_char:
    shows "t \<star> u \<noteq> V.null \<longleftrightarrow> V.arr t \<and> V.arr u \<and> Dom t = Cod u"
      using hcomp_def null_char by auto

    lemma objI [intro]:
    assumes "t \<noteq> V.null"
    and "Dom t \<in> Obj" and "Cod t = Dom t" and "Trn t = Id (Dom t)"
    shows "H.ide t"
      using assms
      by (metis Comp_Hom_Id Comp_Id_Hom H.ide_def MkArr_Trn
          V.ide_implies_arr arrE hcomp_def ide_Id null_coincidence\<^sub>C\<^sub>R\<^sub>C staI)

    lemma objE [elim]:
    assumes "H.ide a"
    and "\<lbrakk>a \<noteq> V.null; Dom a \<in> Obj; Cod a = Dom a; Trn a = Id (Dom a)\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms
      by (metis Cod.simps(1) Dom.simps(1) H.ide_def H_composable_char
          Trn.simps(1) arr.simps(2) arr_char null_char null_coincidence\<^sub>C\<^sub>R\<^sub>C objI)

    definition mkobj
    where "mkobj A \<equiv> MkArr A A (Id A)"

    lemma mkobj_simps [simp]:
    shows "Dom (mkobj A) = A" and "Cod (mkobj A) = A"
    and "Trn (mkobj A) = Id A"
      using mkobj_def by auto

    lemma obj_mkobj:
    assumes "A \<in> Obj"
    shows "H.ide (mkobj A)"
      using assms
      by (simp add: mkobj_def null_char objI)

    lemma obj_char:
    shows "H.ide a \<longleftrightarrow> V.arr a \<and> mkobj (Dom a) = a"
      by (metis H.ide_def H_composable_char MkArr_Trn arrE mkobj_def
          objE obj_mkobj)

    lemma obj_is_sta:
    assumes "H.ide a"
    shows "V.ide a"
      using assms ide_Id by fastforce

    lemma obj_simps:
    assumes "H.ide a"
    shows "Cod a = Dom a" and "Trn a = Id (Dom a)"
      using assms by auto

    lemma domains_char:
    shows "H.domains t = {a. V.arr t \<and> mkobj (Dom t) = a}"
      unfolding H.domains_def
      using H_composable_char obj_char obj_mkobj obj_simps(1) by auto

    lemma codomains_char:
    shows "H.codomains t = {a. V.arr t \<and> mkobj (Cod t) = a}"
      unfolding H.codomains_def
      using H_composable_char obj_char obj_mkobj obj_simps(1) by auto

    lemma H_arr_char:
    shows "H.arr t \<longleftrightarrow> t \<noteq> Null \<and> Dom t \<in> Obj \<and> Cod t \<in> Obj \<and>
                       residuation.arr (Hom (Dom t) (Cod t)) (Trn t)"
      using H.arr_def codomains_char domains_char arr_char by force

    lemma H_arrI [intro]:
    assumes "t \<noteq> V.null" and "Dom t \<in> Obj" and "Cod t \<in> Obj"
    and "residuation.arr (Hom (Dom t) (Cod t)) (Trn t)"
    shows "H.arr t"
      using assms H_arr_char null_char by auto

    lemma H_seq_char:
    shows "H.seq t u \<longleftrightarrow> V.arr t \<and> V.arr u \<and> Dom t = Cod u"
      by (metis H_arr_char H_composable_char arr_char arr_hcomp\<^sub>C\<^sub>R\<^sub>C null_char)

    lemma H_seqI [intro]:
    assumes "V.arr t" and "V.arr u" and "Dom t = Cod u"
    shows "H.seq t u"
      using assms H_seq_char by blast

    sublocale H: category hcomp
    proof
      show "\<And>t u. hcomp t u \<noteq> H.null \<Longrightarrow> H.seq t u"
        using hcomp_def H_seq_char null_char
        by (metis null_coincidence\<^sub>C\<^sub>R\<^sub>C)
      show "\<And>t. (H.domains t \<noteq> {}) = (H.codomains t \<noteq> {})"
        by (simp add: codomains_char domains_char)
      show "\<And>h g f. \<lbrakk>H.seq h g; H.seq (h \<star> g) f\<rbrakk> \<Longrightarrow> H.seq g f"
        using H_seq_char
        by (metis Dom.simps(1) hcomp_def)
      show "\<And>h g f. \<lbrakk>H.seq h (g \<star> f); H.seq g f\<rbrakk> \<Longrightarrow> H.seq h g"
        using H_seq_char
        by (metis Cod.simps(1) hcomp_def)
      show "\<And>g f h. \<lbrakk>H.seq g f; H.seq h g\<rbrakk> \<Longrightarrow> H.seq (h \<star> g) f"
        using H_seq_char
        by (metis Dom.simps(1) arr_hcomp\<^sub>C\<^sub>R\<^sub>C hcomp_def)
      show "\<And>t u v. \<lbrakk>H.seq u v; H.seq t u\<rbrakk> \<Longrightarrow> (t \<star> u) \<star> v = t \<star> u \<star> v"
        using arr_hcomp\<^sub>C\<^sub>R\<^sub>C H_seq_char H_composable_char null_char Comp_assoc
        apply (intro arr_eqI)
            apply auto[4]
        apply auto
        using H_arr_char arr_char by auto
    qed

    lemma is_category:
    shows "category hcomp"
      ..

    lemma arr_coincidence\<^sub>C\<^sub>R\<^sub>C [simp]:
    shows "H.arr = V.arr"
      using H_arr_char arr_char by blast

    lemma dom_char:
    shows "H.dom = (\<lambda>t. if H.arr t then mkobj (Dom t) else V.null)"
      using domains_char H.dom_in_domains H.has_domain_iff_arr H.dom_def
      by auto

    lemma dom_mkobj [simp]:
    assumes "A \<in> Obj"
    shows "H.dom (mkobj A) = mkobj A"
      using assms obj_mkobj by auto

    lemma mkobj_Dom [simp]:
    assumes "H.ide a"
    shows "mkobj (Dom a) = H.dom a"
      using assms obj_char by auto

    lemma cod_char:
    shows "H.cod = (\<lambda>t. if H.arr t then mkobj (Cod t) else V.null)"
      using codomains_char H.cod_in_codomains H.has_codomain_iff_arr H.cod_def
      by auto

    lemma cod_mkobj [simp]:
    assumes "A \<in> Obj"
    shows "H.cod (mkobj A) = mkobj A"
      using assms obj_mkobj by auto

    lemma Dom_dom [simp]:
    assumes "V.arr t"
    shows "Dom (H.dom t) = Dom t"
      using assms dom_char mkobj_def by auto

    lemma Dom_cod [simp]:
    assumes "V.arr t"
    shows "Dom (H.cod t) = Cod t"
      using assms cod_char mkobj_def by auto

    lemma Cod_dom [simp]:
    assumes "V.arr t"
    shows "Cod (H.dom t) = Dom t"
      using assms dom_char mkobj_def by auto

    lemma Cod_cod [simp]:
    assumes "V.arr t"
    shows "Cod (H.cod t) = Cod t"
      using assms cod_char mkobj_def by auto

    lemma con_implies_par:
    assumes "V.con t u"
    shows "H.par t u"
      using assms cod_char dom_char V.con_implies_arr(1-2) con_implies_Par(1-2)
      by auto

    lemma par_resid:
    assumes "V.con t u"
    shows "H.par t (resid t u)"
      using assms cod_char dom_char V.con_implies_arr(1-2) con_implies_Par(1-2)
      by auto

    lemma simulation_dom:
    shows "simulation resid resid H.dom"
      using dom_char arr_char H_arr_char con_char
      apply unfold_locales
        apply presburger
       apply (metis (no_types, lifting) H.arr_dom V.arrE)
      by (metis (no_types, lifting) H.ide_dom par_resid V.ideE obj_is_sta)

    lemma simulation_cod:
    shows "simulation resid resid H.cod"
      using cod_char arr_char H_arr_char con_char
      apply unfold_locales
        apply presburger
       apply (metis (no_types, lifting) H.arr_cod V.arr_def)
      by (metis (no_types, lifting) H.ide_cod par_resid V.ideE obj_is_sta)

    sublocale dom: simulation resid resid H.dom
      using simulation_dom by blast
    sublocale cod: simulation resid resid H.cod
      using simulation_cod by blast

    sublocale VV: fibered_product_rts resid resid resid H.dom H.cod ..

    sublocale H\<^sub>V\<^sub>V: simulation VV.resid resid
                     \<open>\<lambda>t. if VV.arr t then fst t \<star> snd t else V.null\<close>
    proof
      let ?C = "\<lambda>t. if VV.arr t then fst t \<star> snd t else V.null"
      show "\<And>t. \<not> VV.arr t \<Longrightarrow> ?C t = V.null"
        by simp
      fix t u
      assume tu: "VV.con t u"
      have arr_t: "VV.arr t" and arr_u: "VV.arr u"
        using tu VV.con_implies_arr by blast+
      have t: "V.arr (fst t) \<and> V.arr (snd t) \<and> Dom (fst t) = Cod (snd t)"
        by (metis Cod_cod Cod_dom VV.arr_char arr_t)
      have u: "V.arr (fst u) \<and> V.arr (snd u) \<and> Dom (fst u) = Cod (snd u)"
        by (metis Cod_cod Cod_dom VV.arr_char arr_u)
      let ?a = "Dom (snd t)" and ?b = "Cod (snd t)" and ?c = "Cod (fst t)"
      have a: "?a \<in> Obj" and b: "?b \<in> Obj" and c: "?c \<in> Obj"
        using tu VV.con_char VV.con_implies_arr sta_char arr_char by fast+
      interpret AB: extensional_rts \<open>Hom ?a ?b\<close>
        using a b rts_Hom by simp
      interpret BC: extensional_rts \<open>Hom ?b ?c\<close>
        using b c rts_Hom by simp
      interpret AC: extensional_rts \<open>Hom ?a ?c\<close>
        using a c rts_Hom by simp
      interpret BCxAB: product_rts \<open>Hom ?b ?c\<close> \<open>Hom ?a ?b\<close> ..
      interpret Comp: binary_simulation \<open>Hom ?b ?c\<close> \<open>Hom ?a ?b\<close> \<open>Hom ?a ?c\<close>
                        \<open>\<lambda>(t', u'). Comp ?a ?b ?c t' u'\<close>
        using a b c binary_simulation_Comp by simp
      have 0: "BCxAB.con (Trn (fst t), Trn (snd t)) (Trn (fst u), Trn (snd u))"
        by (metis BCxAB.con_char VV.con_char con_char fst_conv snd_conv t tu)
      have 1: "Dom (snd u) = ?a" and 2: "Cod (fst u) = ?c"
      and 3: "Cod (snd u) = ?b"
        using VV.con_char con_char tu by metis+
      show 4: "?C t \<frown> ?C u"
        using a c t u tu 0 1 2 3 VV.arr_char VV.con_char hcomp_def
             AC.con_implies_arr con_char
              Comp.preserves_con
                [of "(Trn (fst t), Trn (snd t))" "(Trn (fst u), Trn (snd u))"]
        by simp
      show "?C (VV.resid t u) = ?C t \\ ?C u"
      proof -
        have Con: "VV.Con t u"
          using tu VV.con_char by blast
        have "?C (VV.resid t u) = fst t \\ fst u \<star> snd t \\ snd u"
          using tu Con VV.arr_char VV.arr_resid VV.resid_def by auto
        also have "... = (fst t \<star> snd t) \\ (fst u \<star> snd u)"
            using t u tu arr_t arr_u 0 1 2 3 4 Con VV.con_char null_char
                  H_composable_char BCxAB.resid_def Comp.preserves_resid
            by (intro arr_eqI) auto
        also have "... = ?C t \\ ?C u"
          using arr_t arr_u by auto
        finally show ?thesis by blast
      qed
    qed

    lemma simulation_hcomp:
    shows "simulation VV.resid resid (\<lambda>t. if VV.arr t then fst t \<star> snd t else V.null)"
      ..

    lemma Dom_src [simp]:
    assumes "V.arr t"
    shows "Dom (V.src t) = Dom t"
      using assms con_implies_Par(1) by simp

    lemma Dom_trg [simp]:
    assumes "V.arr t"
    shows "Dom (V.trg t) = Dom t"
      using assms V.trg_def by simp

    lemma Cod_src [simp]:
    assumes "V.arr t"
    shows "Cod (V.src t) = Cod t"
      using assms con_implies_Par(2) by simp

    lemma Cod_trg [simp]:
    assumes "V.arr t"
    shows "Cod (V.trg t) = Cod t"
      using assms V.trg_def by simp

    lemma dom_src\<^sub>C\<^sub>R\<^sub>C [simp]:
    shows "H.dom (V.src t) = H.dom t"
      by (metis V.arr_src_iff_arr V.con_arr_src(2) con_implies_par dom.extensional)

    lemma dom_trg\<^sub>C\<^sub>R\<^sub>C [simp]:
    shows "H.dom (V.trg t) = H.dom t"
      by (metis H.dom_dom V.arr_def V.trg_def dom.extensional null_char
          par_resid trg_char)

    lemma cod_src\<^sub>C\<^sub>R\<^sub>C [simp]:
    shows "H.cod (V.src t) = H.cod t"
      by (simp add: cod_char V.arr_src_iff_arr)

    lemma cod_trg\<^sub>C\<^sub>R\<^sub>C [simp]:
    shows "H.cod (V.trg t) = H.cod t"
      by (simp add: cod_char V.arr_trg_iff_arr)

    lemma src_dom\<^sub>C\<^sub>R\<^sub>C [simp]:
    shows "V.src (H.dom t) = H.dom t"
      by (metis H.ide_dom dom_char V.src_ide arr_char src_char null_char obj_is_sta)

    lemma trg_dom\<^sub>C\<^sub>R\<^sub>C [simp]:
    shows "V.trg (H.dom t) = H.dom t"
      by (metis H.cod_dom V.ide_iff_src_self V.trg_ide cod.extensional
          null_char src_dom\<^sub>C\<^sub>R\<^sub>C trg_char)

    lemma src_cod\<^sub>C\<^sub>R\<^sub>C [simp]:
    shows "V.src (H.cod t) = H.cod t"
      by (metis H.dom_cod src_dom\<^sub>C\<^sub>R\<^sub>C)

    lemma trg_cod\<^sub>C\<^sub>R\<^sub>C [simp]:
    shows "V.trg (H.cod t) = H.cod t"
      by (metis cod.extensional cod.preserves_trg cod_trg\<^sub>C\<^sub>R\<^sub>C dom.extensional
          trg_dom\<^sub>C\<^sub>R\<^sub>C)

    sublocale rts_category resid hcomp
      by unfold_locales auto

    proposition is_rts_category:
    shows "rts_category resid hcomp"
      ..

    text\<open>
      The elements of the originally given set \<open>Obj\<close> are in bijective correspondence
      with the objects of the constructed RTS-category.
    \<close>

    lemma bij_mkobj:
    shows "mkobj \<in> Obj \<rightarrow> Collect obj"
    and "Dom \<in> Collect obj \<rightarrow> Obj"
    and "\<And>A. Dom (mkobj A) = A"
    and "\<And>a. obj a \<Longrightarrow> mkobj (Dom a) = a"
    and "bij_betw mkobj Obj (Collect obj)"
    and "bij_betw Dom (Collect obj) Obj"
      using obj_mkobj obj_char arr_char
      apply auto[6]
      by (intro bij_betwI, auto)+

    abbreviation MkArr\<^sub>e\<^sub>x\<^sub>t
    where "MkArr\<^sub>e\<^sub>x\<^sub>t A B \<equiv>
           \<lambda>t. if residuation.arr (Hom A B) t then MkArr A B t else Null"

    abbreviation Trn\<^sub>e\<^sub>x\<^sub>t
    where "Trn\<^sub>e\<^sub>x\<^sub>t a b \<equiv>
           \<lambda>t. if residuation.arr (HOM a b) t then Trn t
               else ResiduatedTransitionSystem.partial_magma.null
                     (Hom (Dom a) (Dom b))"

    lemma inverse_simulations_Trn_MkArr:
    assumes "A \<in> Obj" and "B \<in> Obj"
    shows "inverse_simulations (Hom A B) (HOM (mkobj A) (mkobj B))
             (Trn\<^sub>e\<^sub>x\<^sub>t (mkobj A) (mkobj B)) (MkArr\<^sub>e\<^sub>x\<^sub>t A B)"
    proof -
      interpret Hom_AB: rts \<open>Hom A B\<close>
        using assms
        by (simp add: extensional_rts.axioms(1) rts_Hom)
      let ?a = "mkobj A" and ?b = "mkobj B"
      let ?F = "MkArr\<^sub>e\<^sub>x\<^sub>t A B"
      let ?G = "Trn\<^sub>e\<^sub>x\<^sub>t (mkobj A) (mkobj B)"
      have a: "obj ?a" and b: "obj ?b"
        using assms obj_char obj_mkobj by auto
      interpret HOM_ab: sub_rts resid \<open>\<lambda>t. \<guillemotleft>t : ?a \<rightarrow> ?b\<guillemotright>\<close>
        using assms sub_rts_HOM by simp
      interpret F: simulation \<open>Hom A B\<close> \<open>HOM ?a ?b\<close> ?F
        using assms a b HOM_ab.con_char HOM_ab.null_char null_char
              Hom_AB.con_implies_arr(1-2) H.in_homI cod_char dom_char arr_char
              HOM_ab.resid_def con_char
        by unfold_locales auto
      interpret G: simulation \<open>HOM ?a ?b\<close> \<open>Hom A B\<close> ?G
      proof
        show "\<And>t. \<not> HOM_ab.arr t \<Longrightarrow> Trn\<^sub>e\<^sub>x\<^sub>t ?a ?b t = Hom_AB.null"
          by simp
        fix t u
        assume tu: "HOM_ab.con t u"
        show con: "Hom_AB.con (?G t) (?G u)"
          using assms a b tu HOM_ab.arr_char HOM_ab.con_char con_char
          apply auto[1]
          by (metis Cod.simps(1) Cod_cod Cod_dom H.in_homE arr_char mkobj_def)
        show "?G (HOM ?a ?b t u) = Hom A B (?G t) (?G u)"
          using assms tu con HOM_ab.con_char HOM_ab.resid_def HOM_ab.resid_closed
          apply auto[1]
          by (metis Cod_dom Dom_cod H.in_homE HOM_ab.inclusion mkobj_simps(1-2))
      qed
      show "inverse_simulations (Hom A B) (HOM ?a ?b) ?G ?F"
      proof
        show "?F \<circ> ?G = I HOM_ab.resid"
        proof
          fix t
          show "(?F \<circ> ?G) t = I HOM_ab.resid t"
            using assms a b MkArr_Trn HOM_ab.arr_char HOM_ab.null_char
                  arr_char null_char
            apply auto[1]
             apply (metis Cod_dom Dom_cod H.in_homE HOM_ab.inclusion mkobj_simps(1-2))
            by (metis Cod_dom Dom_cod H.in_homE H_arr_char mkobj_simps(1-2))
        qed
        show "?G \<circ> ?F = I (Hom A B)"
          using assms a b by auto
      qed
    qed

    text\<open>
      Each hom-RTS of the constructed RTS-category is isomorphic to the corresponding
      RTS given by \<open>Hom\<close>.
    \<close>

    lemma isomorphic_rts_Hom_HOM:
    assumes "A \<in> Obj" and "B \<in> Obj"
    shows "isomorphic_rts (Hom A B) (HOM (mkobj A) (mkobj B))"
      using assms inverse_simulations_Trn_MkArr isomorphic_rts_def by blast

  end

end
