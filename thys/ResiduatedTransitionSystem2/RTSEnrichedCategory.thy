(*  Title:       RTSEnrichedCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2024
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "RTS-Enriched Categories"

 text \<open>
   The category \<open>\<^bold>R\<^bold>T\<^bold>S\<close> is cartesian closed, hence monoidal closed.
   This implies that each hom-set of \<open>\<^bold>R\<^bold>T\<^bold>S\<close> itself carries the structure of an RTS,
   so that \<open>\<^bold>R\<^bold>T\<^bold>S\<close> becomes a category ``enriched in itself''.
   In this section we show that RTS-categories are essentially the same thing as
   categories enriched in \<open>\<^bold>R\<^bold>T\<^bold>S\<close>, and that the RTS-category \<open>\<^bold>R\<^bold>T\<^bold>S\<^sup>\<dagger>\<close> is equivalent to
   the RTS-category determined by \<open>\<^bold>R\<^bold>T\<^bold>S\<close> regarded as a category enriched in itself.
   Thus, the complete structure of the RTS-category \<open>\<^bold>R\<^bold>T\<^bold>S\<^sup>\<dagger>\<close> is already determined by
   its ordinary subcategory \<open>\<^bold>R\<^bold>T\<^bold>S\<close>.
 \<close>

theory RTSEnrichedCategory
imports RTSCatx RTSCat EnrichedCategoryBasics.CartesianClosedMonoidalCategory
        EnrichedCategoryBasics.EnrichedCategory
begin

  context rtscat
  begin

    (*
      TODO: There are currently definitions in @{locale cartesian_monoidal_category} that
      conflict with definitions in @{locale elementary_cartesian_closed_monoidal_category}.
      To make the interpretation of @{locale elementary_cartesian_closed_monoidal_category},
      we have to import the former using qualified names to avoid the clashes.
      At some point I will hopefully settle on a good systematic way to combine locales
      with a minimum of such clashes, but this is a stopgap for now.
    *)

    sublocale CMC: cartesian_monoidal_category comp Prod \<alpha> \<iota>
      using extends_to_cartesian_monoidal_category\<^sub>E\<^sub>C\<^sub>C by blast

    text \<open>
      The tensor for @{locale elementary_cartesian_closed_monoidal_category} is given by the
      binary functor \<open>Prod\<close>.  This functor is defined in uncurried form, which is consistent
      with its nature as a functor defined on a product category.  However, the tensor
      @{term CMC.tensor} defined in @{locale monoidal_category} is a curried version.
      There might be a way to streamline this, if the various monoidal category locales were
      changed so that the binary functor used to specify the tensor were given in curried form,
      but I have not yet attempted to do this. For now, we have two versions of tensor,
      which we need to show are equal to each other.
    \<close>

    lemma tensor_agreement:
    assumes "arr f" and "arr g"
    shows "CMC.tensor f g = f \<otimes> g"
      by simp

    text \<open>
      The situation with tupling and ``duplicators'' is similar.
    \<close>

    lemma tuple_agreement:
    assumes "span f g"
    shows "CMC.tuple f g = \<langle>f, g\<rangle>"
    proof (intro pr_joint_monic [of "cod f" "cod g" "CMC.tuple f g" "\<langle>f, g\<rangle>"])
      show "ide (cod f)" and "ide (cod g)"
        using assms by auto
      show "seq \<pp>\<^sub>0[cod f, cod g] (CMC.tuple f g)"
        by (metis (no_types, lifting) CMC.ECC.seq_pr_tuple \<open>ide (cod f)\<close>
            \<open>ide (cod g)\<close> assms pr_agreement(1))
      show "\<pp>\<^sub>0[cod f, cod g] \<cdot> CMC.tuple f g = \<pp>\<^sub>0[cod f, cod g] \<cdot> \<langle>f, g\<rangle>"
        using assms pr_agreement(1-2)
        by (metis (no_types, lifting) CMC.ECC.pr_tuple(2) \<open>ide (cod f)\<close>
            \<open>ide(cod g)\<close> pr_tuple(2))
      show "\<pp>\<^sub>1[cod f, cod g] \<cdot> CMC.tuple f g = \<pp>\<^sub>1[cod f, cod g] \<cdot> \<langle>f, g\<rangle>"
        using assms pr_agreement(1-2)
        by (metis (no_types, lifting) CMC.ECC.pr_tuple(1) \<open>ide (cod f)\<close>
            \<open>ide (cod g)\<close> pr_tuple(1))
    qed

    lemma dup_agreement:
    assumes "arr f"
    shows "CMC.dup f = dup f"
      using assms tuple_agreement by simp

    sublocale elementary_cartesian_closed_monoidal_category
                comp Prod \<alpha> \<iota> exp eval curry
      using extends_to_elementary_cartesian_closed_monoidal_category\<^sub>E\<^sub>C\<^sub>C\<^sub>C
      by blast

    text \<open>
      We have a need for the following expansion of associators in terms of tensor and
      projections.  This is actually the definition of the associators given
      in @{locale category_with_binary_products}, but it could (and perhaps should) be proved
      as a consequence of the locale assumptions in @{locale elementary_cartesian_category}.
      Here we already have the fact \<open>assoc_agreement\<close> which expresses that the definition
      of associators given in @{locale category_with_binary_products} agrees with the version
      derived from the locale parameters in @{locale cartesian_monoidal_category},
      and \<open>prod_eq_tensor\<close>, which expresses that the tensor equals the cartesian product.
      So we can just use these facts, together with the definition from
      @{locale elementary_cartesian_category}, to avoid a longer proof.
    \<close>

    lemma assoc_expansion:
    assumes "ide a" and "ide b" and "ide c"
    shows "CMC.assoc a b c =
           \<langle>\<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<langle>\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<pp>\<^sub>0[a \<otimes> b, c]\<rangle> \<rangle>"
      using assms assoc_def assoc_agreement by simp

    (* TODO: After removing clashes, there is an ECMC qualifier that I don't really want. *)
    lemma extends_to_enriched_category:
    shows "enriched_category comp Prod \<alpha> \<iota>
             (Collect ide) exp ECMC.Id ECMC.Comp"
      using ECMC.is_enriched_in_itself by blast

  end

  locale rts_enriched_category =
    universe arr_type +
    RTS: rtscat arr_type +
    enriched_category RTS.comp RTS.Prod RTS.\<alpha> RTS.\<iota> Obj Hom Id Comp
  for arr_type :: "'A itself"
  and Obj :: "'O set"
  and Hom :: "'O \<Rightarrow> 'O \<Rightarrow> 'A rtscatx.arr"
  and Id :: "'O \<Rightarrow> 'A rtscatx.arr"
  and Comp :: "'O \<Rightarrow> 'O \<Rightarrow> 'O \<Rightarrow> 'A rtscatx.arr"
  begin

    (*
     * TODO: The subscripts are needed to avoid a later clash with
     * sublocale declarations.  Qualified names can be used instead,
     * but the result seems to be worse.
     *)
    abbreviation HOM\<^sub>E\<^sub>C
    where "HOM\<^sub>E\<^sub>C a b \<equiv> RTS.Rts (Hom a b)"

  end

  locale hom_rts =
    rts_enriched_category +
  fixes a :: 'b
  and b :: 'b
  assumes a: "a \<in> Obj"
  and b: "b \<in> Obj"
  begin

    sublocale extensional_rts \<open>HOM\<^sub>E\<^sub>C a b\<close>
      using a b by force

    sublocale small_rts \<open>HOM\<^sub>E\<^sub>C a b\<close>
      using a b by force

  end

  locale rts_enriched_functor =
    RTS: rtscat arr_type +
    A: rts_enriched_category arr_type Obj\<^sub>A Hom\<^sub>A Id\<^sub>A Comp\<^sub>A +
    B: rts_enriched_category arr_type Obj\<^sub>B Hom\<^sub>B Id\<^sub>B Comp\<^sub>B +
    enriched_functor RTS.comp RTS.Prod RTS.\<alpha> RTS.\<iota>
  for arr_type :: "'A itself"
  begin

    lemma is_local_simulation:
    assumes "a \<in> Obj\<^sub>A" and "b \<in> Obj\<^sub>A"
    shows "simulation (A.HOM\<^sub>E\<^sub>C a b) (B.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b))
             (RTS.Map (F\<^sub>a a b))"
      using assms preserves_Hom [of a b] RTS.arrD [of "F\<^sub>a a b"] by auto

  end

  locale fully_faithful_rts_enriched_functor =
    rts_enriched_functor +
    fully_faithful_enriched_functor RTS.comp RTS.Prod RTS.\<alpha> RTS.\<iota>

section "RTS-Enriched Categories induce RTS-Categories"

  text\<open>
    Here we show that every RTS-enriched category determines a corresponding RTS-category.
    This is done by combining the RTS's underlying the homs of the RTS-enriched category,
    forming a global RTS that provides the vertical structure of the RTS-category.
    The composition operation of the RTS-enriched category is used to obtain the
    horizontal structure.
  \<close>

  locale rts_category_of_enriched_category =
    universe arr_type +
    RTS: rtscat arr_type +
    rts_enriched_category arr_type Obj Hom Id Comp
  for arr_type :: "'A itself"
  and Obj :: "'O set"
  and Hom :: "'O \<Rightarrow> 'O \<Rightarrow> 'A rtscatx.arr"
  and Id :: "'O \<Rightarrow> 'A rtscatx.arr"
  and Comp :: "'O \<Rightarrow> 'O \<Rightarrow> 'O \<Rightarrow> 'A rtscatx.arr"
  begin

    notation RTS.in_hom    (\<open>\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>\<close>)
    notation RTS.prod      (infixr \<open>\<otimes>\<close> 51)
    notation RTS.one       (\<open>\<one>\<close>)
    notation RTS.assoc     (\<open>\<a>[_, _, _]\<close>)
    notation RTS.lunit     (\<open>\<l>[_]\<close>)
    notation RTS.runit     (\<open>\<r>[_]\<close>)

    text\<open>
      Here we define the ``global RTS'', obtained as the disjoint union of all the
      hom-RTS's.  Note that types 'O and 'A are fixed in the current context:
      type 'O is the type of ``objects'' of the given RTS-enriched category,
      and type 'A is the type of the universe that underlies the base category \<open>RTS\<close>.
    \<close>

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
                     residuation.arr (HOM\<^sub>E\<^sub>C (Dom t) (Cod t)) (Trn t)"

    abbreviation Ide :: "('O, 'A) arr \<Rightarrow> bool"
    where "Ide \<equiv> \<lambda>t. t \<noteq> Null \<and> Dom t \<in> Obj \<and> Cod t \<in> Obj \<and>
                     residuation.ide (HOM\<^sub>E\<^sub>C (Dom t) (Cod t)) (Trn t)"

    definition Con :: "('O, 'A) arr \<Rightarrow> ('O, 'A) arr \<Rightarrow> bool"
    where "Con t u \<equiv> Arr t \<and> Arr u \<and> Dom t = Dom u \<and> Cod t = Cod u \<and>
                     residuation.con (HOM\<^sub>E\<^sub>C (Dom t) (Cod t)) (Trn t) (Trn u)"

    text\<open>
      The global residuation is obtained by combining the local residuations of
      each of the hom-RTS's.
    \<close>

    fun resid  (infix \<open>\\<close> 70)
    where "resid Null u = Null"
        | "resid t Null = Null"
        | "resid t u = (if Con t u
                        then MkArr (Dom t) (Cod t)
                               (HOM\<^sub>E\<^sub>C (Dom t) (Cod t) (Trn t) (Trn u))
                        else Null)"

    sublocale V: ResiduatedTransitionSystem.partial_magma resid
      apply unfold_locales
      by (metis Trn.cases resid.simps(1-2))

    lemma null_char:
    shows "V.null = Null"
      by (metis V.null_is_zero(2) resid.simps(1))

    lemma ConI [intro]:
    assumes "Arr t" and "Arr u" and "Dom t = Dom u" and "Cod t = Cod u"
    and "residuation.con (HOM\<^sub>E\<^sub>C (Dom t) (Cod t)) (Trn t) (Trn u)"
    shows "Con t u"
      using assms Con_def by simp

    lemma ConE [elim]:
    assumes "Con t u"
    and "\<lbrakk>Arr t; Arr u; Dom t = Dom u; Cod t = Cod u;
          residuation.con (HOM\<^sub>E\<^sub>C (Dom t) (Cod t)) (Trn t) (Trn u)\<rbrakk> \<Longrightarrow> T"
    shows T
      using assms Con_def by blast

    lemma Con_sym:
    assumes "Con t u"
    shows "Con u t"
      using assms Con_def extensional_rts_def residuation.con_sym
            rts.axioms(1)
      by fastforce

    lemma resid_ne_Null_imp_Con:
    assumes "t \\ u \<noteq> Null"
    shows "Con t u"
      using assms resid.elims by metis
 
    sublocale V: residuation resid
    proof
      fix t u :: "('O, 'A) arr"
      assume tu: "t \\ u \<noteq> V.null"
      interpret hom: hom_rts arr_type Obj Hom Id Comp \<open>Dom t\<close> \<open>Cod t\<close>
        using tu null_char resid_ne_Null_imp_Con
        by unfold_locales auto
      show "t \\ u \<noteq> V.null \<Longrightarrow> u \\ t \<noteq> V.null"
        using tu null_char Con_sym
        apply (cases t; cases u)
           apply simp_all
        by metis
      show "(t \\ u) \\ (t \\ u) \<noteq> V.null"
        using tu null_char hom.arr_resid hom.con_arr_self Con_def
        apply (cases t; cases u)
           apply simp_all
        by metis
      next
      fix t u v :: "('O, 'A) arr"
      assume tuv: "(v \\ t) \\ (u \\ t) \<noteq> V.null"
      have tu: "Con t u"
        using tuv null_char Con_sym resid_ne_Null_imp_Con
        by (metis Con_def)
      have tv: "Con t v"
        using tuv null_char Con_sym resid_ne_Null_imp_Con
        by (metis Con_def)
      interpret hom: hom_rts arr_type Obj Hom Id Comp \<open>Dom t\<close> \<open>Cod t\<close>
        using tu null_char arr.exhaust resid.simps(1-3)
           apply unfold_locales
        by blast+
      show "(v \\ t) \\ (u \\ t) = (v \\ u) \\ (t \\ u)"
      proof -
        have "\<And>td tc tt ud uc ut vd vc vt.
                 \<lbrakk>t = MkArr td tc tt; u = MkArr ud uc ut; v = MkArr vd vc vt\<rbrakk>
                    \<Longrightarrow> ?thesis"
        proof -
          fix td tc tt ud uc ut vd vc vt
          assume t: "t = MkArr td tc tt"
          assume u: "u = MkArr ud uc ut"
          assume v: "v = MkArr vd vc vt"
          show "(v \\ t) \\ (u \\ t) = (v \\ u) \\ (t \\ u)"
            using t u v tu tv tuv Con_def hom.cube null_char
            apply auto[1]
            by (metis Cod.simps(1) Dom.simps(1) hom.con_sym hom.arr_resid
              hom.arr_resid_iff_con hom.resid_reflects_con)+
        qed
        thus ?thesis
          using tu tv tuv hom.cube hom.arr_resid_iff_con hom.resid_reflects_con
                null_char resid_ne_Null_imp_Con
          apply (cases v, blast)
          apply (cases u, blast)
          apply (cases t, blast)
          by metis
      qed
    qed

    notation V.con  (infix \<open>\<frown>\<close> 50)

    lemma con_char:
    shows "t \<frown> u \<longleftrightarrow> Con t u"
    proof
      show "t \<frown> u \<Longrightarrow> Con t u"
        using null_char resid_ne_Null_imp_Con by auto
      show "Con t u \<Longrightarrow> t \<frown> u"
        using null_char
        by (cases t; cases u) auto
    qed

    lemma arr_char:
    shows "V.arr t \<longleftrightarrow> Arr t"
      by (metis Con_def RTS.ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C V.arr_def con_char extensional_rts.axioms(1)
          ide_Hom residuation.arrE rts.axioms(1))

    lemma ide_char:
    shows "V.ide t \<longleftrightarrow> Ide t"
    proof (cases "V.arr t")
      show "\<not> V.arr t \<Longrightarrow> ?thesis"
        by (metis RTS.ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C V.arrI V.ide_def arr_char ide_Hom
            residuation.ide_implies_arr rts.axioms(1) small_rts_def)
      assume t: "V.arr t"
      interpret hom: hom_rts arr_type Obj Hom Id Comp \<open>Dom t\<close> \<open>Cod t\<close>
        using t arr_char
        by unfold_locales auto
      show ?thesis
        using t null_char con_char V.ide_def arr_char hom.ide_def
        by (cases t) auto
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
    shows "Trn (t \\ u) = HOM\<^sub>E\<^sub>C (Dom t) (Cod t) (Trn t) (Trn u)"
      using assms con_char
      by (cases t; cases u) auto

    text\<open>
      Targets of arrows of the global RTS agree with the local
      versions from which they were derived.
      The same will be shown for sources below.
    \<close>

    lemma trg_char:
    shows "V.trg t = (if V.arr t
                      then MkArr (Dom t) (Cod t)
                             (residuation.trg (HOM\<^sub>E\<^sub>C (Dom t) (Cod t)) (Trn t))
                      else Null)"
    proof (cases "V.arr t")
      show "\<not> V.arr t \<Longrightarrow> ?thesis"
        using V.con_def V.trg_def null_char by auto
      show "V.arr t \<Longrightarrow> ?thesis"
        using null_char V.not_arr_null
        apply (cases t)
         apply auto[1]
        by (metis (no_types, lifting) RTS.ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C V.arrE V.trg_def
            arr_char con_char ide_Hom resid.simps(3)
            residuation.resid_arr_self rts.axioms(1) small_rts_def)
    qed

    sublocale rts resid
    proof
      show "\<And>t. V.arr t \<Longrightarrow> V.ide (V.trg t)"
        by (simp add: arr_char extensional_rts.axioms(1) ide_char
            rts.ide_trg trg_char)
      show 1: "\<And>a t. \<lbrakk>V.ide a; t \<frown> a\<rbrakk> \<Longrightarrow> t \\ a = t"
      proof -
        fix a t
        assume a: "V.ide a"
        assume con: "t \<frown> a"
        have "t \\ a \<noteq> Null \<and> t \<noteq> Null"
          using con null_char by auto
        moreover have "Dom (t \\ a) = Dom t \<and> Cod (t \\ a) = Cod t"
          using a con ide_char con_char Con_def
          by (metis V.arrE V.arr_resid_iff_con V.con_sym V.cube V.ideE)
        moreover have "Trn (t \\ a) = Trn t"
          using a con ide_char con_char small_rts_def Con_def
          by (metis (no_types, lifting) RTS.ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C(1) Trn_resid ide_Hom
              rts.resid_arr_ide)
        ultimately show "t \\ a = t"
          by (metis Cod.elims Dom.simps(1) Trn.simps(1))
      qed
      show "\<And>a t. \<lbrakk>V.ide a; a \<frown> t\<rbrakk> \<Longrightarrow> V.ide (a \\ t)"
        using ide_char con_char
        by (metis 1 V.arr_resid V.con_arr_self V.con_sym V.cube V.ideE V.ideI)
      show "\<And>t u. t \<frown> u \<Longrightarrow> \<exists>a. V.ide a \<and> a \<frown> t \<and> a \<frown> u"
      proof -
        fix t u
        assume tu: "t \<frown> u"
        interpret hom: hom_rts arr_type Obj Hom Id Comp \<open>Dom t\<close> \<open>Cod t\<close>
          using tu con_char arr_char
          by unfold_locales blast+
        have 1: "hom.con (Trn t) (Trn u)"
          using tu con_char by auto
        obtain \<alpha> where \<alpha>: "hom.ide \<alpha> \<and> hom.con \<alpha> (Trn t) \<and> hom.con \<alpha> (Trn u)"
          using 1 hom.con_imp_coinitial_ax by auto
        have "V.ide (MkArr (Dom t) (Cod t) \<alpha>)"
          using tu \<alpha> V.con_implies_arr arr_char ide_char by auto
        moreover have "MkArr (Dom t) (Cod t) \<alpha> \<frown> t \<and>
                         MkArr (Dom t) (Cod t) \<alpha> \<frown> u"
          using \<alpha> tu con_char hom.ide_implies_arr Con_def by auto
        ultimately show "\<exists>a. V.ide a \<and> V.con a t \<and> V.con a u" by blast
      qed
      show "\<And>t u v. \<lbrakk>V.ide (t \\ u); u \<frown> v\<rbrakk> \<Longrightarrow> t \\ u \<frown> v \\ u"
      proof -
        fix t u v
        assume tu: "V.ide (t \\ u)"
        assume uv: "u \<frown> v"
        have 1: "t \\ u \<noteq> V.null"
          using tu by auto
        interpret hom: hom_rts arr_type Obj Hom Id Comp \<open>Dom t\<close> \<open>Cod t\<close>
          using 1 con_char arr_char
          by unfold_locales blast+
        have "hom.con (HOM\<^sub>E\<^sub>C (Dom t) (Cod t) (Trn t) (Trn u))
                      (HOM\<^sub>E\<^sub>C (Dom t) (Cod t) (Trn v) (Trn u))"
        proof -
          have "hom.con (Trn t) (Trn u)"
            using tu 1 con_char by auto
          have "hom.ide (HOM\<^sub>E\<^sub>C (Dom t) (Cod t) (Trn t) (Trn u))"
            using tu 1 ide_char Dom.simps(1) Cod.simps(1) Trn.simps(1) V.conI
            by auto
          moreover have "hom.con (Trn u) (Trn v)"
            using uv con_char 1 V.conI Con_def by fastforce
          ultimately show ?thesis
            using hom.con_target by blast
        qed
        thus "t \\ u \<frown> v \\ u"
          unfolding con_char Con_def
          using tu uv 1 null_char V.arr_resid arr_char V.ide_implies_arr
          apply clarsimp
          apply (intro conjI) (* 7 goals *)
          subgoal by (meson V.con_sym)
          subgoal using V.arr_resid V.con_sym by meson
          by (metis (mono_tags, lifting) Cod_resid Dom_resid Trn_resid
              V.conI V.con_sym con_implies_Par(1-2))+
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
      interpret hom: hom_rts arr_type Obj Hom Id Comp \<open>Dom t\<close> \<open>Cod t\<close>
        using 1 con_char arr_char [of t]
        by unfold_locales blast+
      have "t \<noteq> Null \<and> u \<noteq> Null"
        using tu con_char by fastforce
      moreover have "Dom t = Dom u \<and> Cod t = Cod u"
        using tu 1 con_char by blast
      moreover have "Trn t = Trn u"
        by (metis Cod_resid Dom_resid Trn_resid calculation(2)
            hom.extensional ide_char prfx_implies_con tu)
      ultimately show "t = u"
        by (cases t; cases u) auto
    qed

    lemma is_extensional_rts:
    shows "extensional_rts resid"
      ..

    lemma arr_MkArr [intro]:
    assumes "a \<in> Obj" and "b \<in> Obj"
    and "residuation.arr (HOM\<^sub>E\<^sub>C a b) t"
    shows "V.arr (MkArr a b t)"
      using assms arr_char by auto

    lemma arr_eqI:
    assumes "t \<noteq> V.null" and "u \<noteq> V.null"
    and "Dom t = Dom u" and "Cod t = Cod u" and "Trn t = Trn u"
    shows "t = u"
      using assms null_char
      by (metis Cod.elims Dom.simps(1) Trn.simps(1))

    lemma MkArr_Trn:
    assumes "V.arr t"
    shows "t = MkArr (Dom t) (Cod t) (Trn t)"
      using assms null_char V.not_arr_null
      by (intro arr_eqI) auto

    lemma src_char:
    shows "V.src t = (if V.arr t
                      then MkArr (Dom t) (Cod t)
                             (weakly_extensional_rts.src
                                (HOM\<^sub>E\<^sub>C (Dom t) (Cod t)) (Trn t))
                      else Null)"
    proof (cases "V.arr t")
      show "\<not> V.arr t \<Longrightarrow> ?thesis"
        using null_char V.src_def by presburger
      assume t: "V.arr t"
      show ?thesis
      proof -
        interpret Hom: extensional_rts \<open>RTS.Rts (Hom (Dom t) (Cod t))\<close>
          using t ide_Hom arr_char RTS.ide_char RTS.arrD by metis
        have "V.ide (MkArr (Dom t) (Cod t) (Hom.src (Trn t)))"
          unfolding ide_char
          using t arr_char by auto
        moreover have "t \<frown> MkArr (Dom t) (Cod t) (Hom.src (Trn t))"
          using t MkArr_Trn con_char Con_def by auto
        ultimately show ?thesis
          using V.sources_char V.src_in_sources by auto
      qed
    qed

    text\<open>
      Here we use the composition operation of the original RTS-enriched category
      to define horizontal composition of transitions of the global RTS.
      Note that a pair of transitions (which comprise a transition of a product RTS)
      must be ``packed'' into a single transition of the RTS underlying a product object,
      before the composition operation can be applied.
    \<close>

    definition hcomp  (infixr \<open>\<star>\<close> 53)
    where "t \<star> u \<equiv>
           if V.arr t \<and> V.arr u \<and> Dom t = Cod u
           then MkArr (Dom u) (Cod t)
                      (RTS.Map (Comp (Dom u) (Cod u) (Cod t))
                               (RTS.Pack (Hom (Dom t) (Cod t))
                                         (Hom (Dom u) (Cod u))
                                         (Trn t, Trn u)))
                    else V.null"

    lemma arr_hcomp:
    assumes "V.arr t" and "V.arr u" and "Dom t = Cod u"
    shows "V.arr (t \<star> u)"
    proof -
      let ?a = "Dom u" and ?b = "Cod u" and ?c = "Cod t"
      have a: "?a \<in> Obj" and b: "?b \<in> Obj" and c: "?c \<in> Obj"
        using assms arr_char by auto
      interpret HOM_ab: hom_rts arr_type Obj Hom Id Comp ?a ?b
        using a b by unfold_locales auto
      interpret HOM_bc: hom_rts arr_type Obj Hom Id Comp ?b ?c
        using b c by unfold_locales auto
      interpret HOM_ac: hom_rts arr_type Obj Hom Id Comp ?a ?c
        using a c by unfold_locales auto
      interpret bcxab: extensional_rts \<open>RTS.Rts (Hom ?b ?c \<otimes> Hom ?a ?b)\<close>
        using a b c by auto
      interpret BCxAB: product_rts \<open>HOM\<^sub>E\<^sub>C ?b ?c\<close> \<open>HOM\<^sub>E\<^sub>C ?a ?b\<close> ..
      interpret Pack: simulation
                        BCxAB.resid \<open>RTS.Rts (Hom ?b ?c \<otimes> Hom ?a ?b)\<close>
                        \<open>RTS.Pack (Hom ?b ?c) (Hom ?a ?b)\<close>
        using a b c RTS.simulation_Pack by blast
      let ?tu = "MkArr ?a ?c
                   (RTS.Map (Comp ?a ?b ?c)
                      (RTS.Pack (Hom ?b ?c) (Hom ?a ?b) (Trn t, Trn u)))"
      have arr_Trn_u: "HOM_ab.arr (Trn u)"
        using assms arr_char by blast
      have arr_Trn_t: "HOM_bc.arr (Trn t)"
        using assms arr_char by simp
      have "V.arr ?tu"
      proof
        show "Dom u \<in> Obj"
          using assms arr_char by auto
        show "Cod t \<in> Obj"
          using assms arr_char by simp
        show "HOM_ac.arr (RTS.Map (Comp ?a ?b ?c)
                            (RTS.Pack (Hom ?b ?c) (Hom ?a ?b)
                               (Trn t, Trn u)))"
        proof -
          have "HOM_ac.arr (RTS.Map (Comp ?a ?b ?c)
                              (RTS.Pack (Hom ?b ?c) (Hom ?a ?b)
                                 (Trn t, Trn u)))"
          proof -
            have "RTS.in_hom (Comp (Dom u) (Cod u) (Cod t))
                             (Hom ?b ?c \<otimes> Hom ?a ?b)
                             (Hom (Dom u) (Cod t))"
              using a b c Comp_in_hom by auto
            moreover have "bcxab.arr
                             (RTS.Pack (Hom ?b ?c) (Hom ?a ?b) (Trn t, Trn u))"
              using a b c arr_Trn_t arr_Trn_u Pack.preserves_reflects_arr
              by auto
            ultimately show ?thesis
              by (metis (mono_tags, lifting) HOM_ac.arrI RTS.in_homE
                  bcxab.arrE RTS.arrD(3) simulation.preserves_con)
          qed
          thus ?thesis by simp
        qed
      qed
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
    shows "Trn (t \<star> u) =
           RTS.Map (Comp (Dom u) (Cod u) (Cod t))
             (RTS.Pack (Hom (Cod u) (Cod t)) (Hom (Dom u) (Cod u))
             (Trn t, Trn u))"
      using assms hcomp_def by auto

    lemma hcomp_Null [simp]:
    shows "t \<star> Null = Null" and "Null \<star> u = Null"
      using hcomp_def null_char by fastforce+

    sublocale H: Category.partial_magma hcomp
      using hcomp_def
      by (metis Category.partial_magma.intro V.not_arr_null)

    lemma H_null_char:
    shows "H.null = V.null"
      using hcomp_def
      by (metis H.null_eqI V.not_arr_null)

    sublocale H: partial_composition hcomp ..

    lemma H_composable_char:
    shows "t \<star> u \<noteq> V.null \<longleftrightarrow> V.arr t \<and> V.arr u \<and> Dom t = Cod u"
      using hcomp_def null_char
      by (cases t; cases u) auto

    definition horizontal_unit
    where "horizontal_unit a \<equiv>
           V.arr a \<and> Dom a = Cod a \<and>
             (\<forall>t. (V.arr t \<and> Dom t = Cod a \<longrightarrow> t \<star> a = t) \<and>
             (V.arr t \<and> Dom a = Cod t \<longrightarrow> a \<star> t = t))"

    lemma H_ide_char:
    shows "H.ide a \<longleftrightarrow> horizontal_unit a"
      using H.ide_def H_composable_char H_null_char horizontal_unit_def
      by fastforce

    text\<open>
      Each \<open>A \<in> Obj\<close> determines a corresponding identity for horizontal composition;
      namely, the transition of \<open>HOM\<^sub>E\<^sub>C A A\<close> obtained by evaluating the simulation
      \<open>\<guillemotleft>Id A : One \<rightarrow> Hom A A\<guillemotright>\<close> at the unique arrow @{term RTS.One.the_arr} of the underlying
      one-arrow RTS of \<open>One\<close>.
    \<close>

    abbreviation mkobj
    where "mkobj A \<equiv> MkArr A A (RTS.Map (Id A) RTS.One.the_arr)"

    lemma Id_yields_horiz_ide:
    assumes "A \<in> Obj"
    shows "H.ide (mkobj A)"
    proof (unfold H.ide_def, intro allI conjI impI)
      interpret HOM_A_A: hom_rts arr_type Obj Hom Id Comp A A
        using assms by unfold_locales
      interpret Id_A: simulation \<open>RTS.Rts \<one>\<close> \<open>HOM\<^sub>E\<^sub>C A A\<close> \<open>RTS.Map (Id A)\<close>
        using assms Id_in_hom [of A] RTS.arrD(3) [of "Id A"] RTS.unity_agreement
        by auto
      let ?a = "mkobj A"
      have "HOM_A_A.ide (RTS.Map (Id A) RTS.One.the_arr)"
        using assms Id_A.preserves_ide RTS.One.ide_char\<^sub>1\<^sub>R\<^sub>T\<^sub>S by auto
      hence a: "V.arr ?a \<and> Dom ?a = Cod ?a"
        using assms ide_char by auto
      show "mkobj A \<star> mkobj A \<noteq> H.null"
        by (metis Cod.simps(1) Dom.simps(1) HOM_A_A.ide_implies_arr H_null_char
            V.not_arr_null \<open>HOM_A_A.ide (RTS.Map (Id A) RTS.One.the_arr)\<close>
            arr_MkArr arr_hcomp assms)
      fix t
      show "t \<star> ?a \<noteq> H.null \<Longrightarrow> t \<star> ?a = t"
      proof -
        assume "t \<star> ?a \<noteq> H.null"
        hence t: "V.arr t \<and> Dom t = Cod ?a"
          by (simp add: H_composable_char H_null_char)
        show "t \<star> ?a = t"
        proof -
          interpret HOM_AB: hom_rts arr_type Obj Hom Id Comp A \<open>Cod t\<close>
            using assms t arr_char
            by unfold_locales auto
          interpret HOM_AB: simulation
                              \<open>HOM\<^sub>E\<^sub>C A (Cod t)\<close> \<open>HOM\<^sub>E\<^sub>C A (Cod t)\<close>
                              \<open>RTS.Map (Hom A (Cod t))\<close>
            using assms t arr_char RTS.arrD [of "Hom A (Cod t)"] by simp
          interpret HOM_ABxI: product_rts \<open>HOM\<^sub>E\<^sub>C A (Cod t)\<close> \<open>RTS.One.resid\<close>
            ..
          interpret HOM_ABxId_A: product_simulation
                                   \<open>HOM\<^sub>E\<^sub>C A (Cod t)\<close> \<open>RTS.Rts \<one>\<close>
                                   \<open>HOM\<^sub>E\<^sub>C A (Cod t)\<close> \<open>HOM\<^sub>E\<^sub>C A A\<close>
                                   \<open>RTS.Map (Hom A (Cod t))\<close> \<open>RTS.Map (Id A)\<close>
            ..
          interpret PU: inverse_simulations
                          \<open>RTS.Rts (Hom A (Cod t) \<otimes> \<one>)\<close> HOM_ABxI.resid
                          \<open>RTS.Pack (Hom A (Cod t)) \<one>\<close>
                          \<open>RTS.Unpack (Hom A (Cod t)) \<one>\<close>
            using assms t arr_char RTS.ide_one
                  RTS.inverse_simulations_Pack_Unpack
                    [of "Hom A (Cod t)" RTS.one]
            by simp
          have "t \<star> ?a \<noteq> Null"
            using a t arr_hcomp null_char arr_char by blast
          moreover have "t \<noteq> Null"
            using t null_char arr_char by blast
          moreover have "Dom t = Dom (hcomp t ?a)"
            using a t hcomp_def by fastforce
          moreover have "Cod t = Cod (hcomp t ?a)"
            using a t hcomp_def by fastforce
          moreover have "Trn t = Trn (hcomp t ?a)"
          proof -
            have "Trn (t \<star> ?a) =
                  (RTS.Map (Comp A A (Cod t)) \<circ>
                     (RTS.Pack (Hom A (Cod t)) (Hom A A) \<circ>
                        HOM_ABxId_A.map))
                     (Trn t, RTS.One.the_arr)"
              using HOM_ABxId_A.map_simp RTS.Map_ide a arr_char t by force
            also have "... =
                  (RTS.Map (Comp A A (Cod t)) \<circ>
                     (RTS.Map (Hom A (Cod t) \<otimes> Id A) \<circ>
                        RTS.Pack (Hom A (Cod t)) \<one>))
                     (Trn t, RTS.One.the_arr)"
            proof -
              have "RTS.Map (Hom A (Cod t) \<otimes> Id A) \<circ>
                      RTS.Pack (Hom A (Cod t)) \<one> =
                    (RTS.Pack (Hom A (Cod t)) (Hom A A) \<circ>
                       HOM_ABxId_A.map \<circ>
                         RTS.Unpack (Hom A (Cod t)) \<one>) \<circ>
                      RTS.Pack (Hom A (Cod t)) \<one>"
                by (metis (no_types, lifting) HOM_AB.b Id_in_hom RTS.Map_prod
                    RTS.ideD(1-3) RTS.in_homE RTS.unity_agreement assms ide_Hom)
              also have "... =
                    (RTS.Pack (Hom A (Cod t)) (Hom A A) \<circ>
                       HOM_ABxId_A.map) \<circ>
                         (RTS.Unpack (Hom A (Cod t)) \<one> \<circ>
                            RTS.Pack (Hom A (Cod t)) \<one>)"
                by auto
              also have "... = RTS.Pack (Hom A (Cod t)) (Hom A A) \<circ>
                                  (HOM_ABxId_A.map \<circ> I HOM_ABxI.resid)"
                using PU.inv by auto
              also have "... = RTS.Pack (Hom A (Cod t)) (Hom A A) \<circ>
                                 HOM_ABxId_A.map"
                using comp_simulation_identity
                        [of "HOM_ABxI.resid" "HOM_ABxId_A.B1xB0.resid"
                            "HOM_ABxId_A.map"]
                      HOM_ABxId_A.simulation_axioms
                by auto
              finally have "RTS.Map (Hom A (Cod t) \<otimes> Id A) \<circ>
                              RTS.Pack (Hom A (Cod t)) \<one> =
                            RTS.Pack (Hom A (Cod t)) (Hom A A) \<circ> HOM_ABxId_A.map"
                by blast
              thus ?thesis by simp
            qed
            also have "... =
                  ((RTS.Map (Comp A A (Cod t)) \<circ>
                      RTS.Map (Hom A (Cod t) \<otimes> Id A)) \<circ>
                        RTS.Pack (Hom A (Cod t)) \<one>)
                     (Trn t, RTS.One.the_arr)"
              by auto
            also have "... =
                  (RTS.Map (Comp A A (Cod t) \<cdot> (Hom A (Cod t) \<otimes> Id A)) \<circ>
                     RTS.Pack (Hom A (Cod t)) \<one>)
                     (Trn t, RTS.One.the_arr)"
              by (metis (no_types, lifting) Comp_Hom_Id HOM_AB.b RTS.CMC.arr_runit
                  RTS.Map_comp assms ide_Hom prod.sel(1-2))
            also have "... = (RTS.Map \<r>[Hom A (Cod t)] \<circ>
                                RTS.Pack (Hom A (Cod t)) \<one>)
                               (Trn t, RTS.One.the_arr)"
              using assms t arr_char Comp_Hom_Id
              by (simp add: RTS.runit_agreement)
            also have "... = (HOM_ABxI.P\<^sub>1 \<circ>
                                (RTS.Unpack (Hom A (Cod t)) \<one> \<circ>
                                   RTS.Pack (Hom A (Cod t)) \<one>))
                               (Trn t, RTS.One.the_arr)"
              using assms t arr_char RTS.Map_runit by auto
            also have "... = HOM_ABxI.P\<^sub>1 (Trn t, RTS.One.the_arr)"
              using assms t arr_char PU.inv HOM_ABxI.P\<^sub>1.simulation_axioms
                    comp_simulation_identity
                      [of "HOM_ABxI.resid" _ "HOM_ABxI.P\<^sub>1"]
              by simp
            also have "... = Trn t"
              using t arr_char HOM_ABxI.P\<^sub>1_def HOM_ABxI.arr_char RTS.One.arr_char
              by auto
            finally show ?thesis by auto
          qed
          ultimately show "t \<star> ?a = t"
            apply (cases t)
            by auto (metis Cod.simps(1) Dom.simps(1) Trn.elims)
        qed
      qed
      show "?a \<star> t \<noteq> H.null \<Longrightarrow> ?a \<star> t = t"
      proof -
        assume "?a \<star> t \<noteq> H.null"
        hence t: "V.arr t \<and> Dom ?a = Cod t"
          by (simp add: H_composable_char H_null_char)
        show "?a \<star> t = t"
        proof -
          interpret HOM_BA: hom_rts arr_type Obj Hom Id Comp \<open>Dom t\<close> A
            using assms t arr_char
            by unfold_locales auto
          interpret HOM_BA: simulation
                              \<open>HOM\<^sub>E\<^sub>C (Dom t) A\<close> \<open>HOM\<^sub>E\<^sub>C (Dom t) A\<close>
                              \<open>RTS.Map (Hom (Dom t) A)\<close>
            using assms t arr_char RTS.arrD(3) [of "Hom (Dom t) A"] by auto
          interpret IxHOM_BA: product_rts
                                \<open>RTS.Rts (RTS.dom \<one>)\<close>
                                \<open>HOM\<^sub>E\<^sub>C (Dom t) A\<close>
            by (metis HOM_BA.small_rts_axioms Id_A.simulation_axioms RTS.ideD(2)
                RTS.ide_one product_rts.intro simulation_def small_rts_def)
          interpret Id_AxHOM_BA: product_simulation
                                   \<open>RTS.Rts (RTS.dom \<one>)\<close> \<open>HOM\<^sub>E\<^sub>C (Dom t) A\<close>
                                   \<open>HOM\<^sub>E\<^sub>C A A\<close> \<open>HOM\<^sub>E\<^sub>C (Dom t) A\<close>
                                   \<open>RTS.Map (Id A)\<close> \<open>RTS.Map (Hom (Dom t) A)\<close>
            by (metis (mono_tags, lifting) HOM_BA.simulation_axioms
                Id_A.simulation_axioms RTS.ideD(2) RTS.ide_one product_rts.intro
                product_simulation_def simulation_def)
          interpret PU: inverse_simulations
                          \<open>RTS.Rts (RTS.dom (\<one> \<otimes> Hom (Dom t) A))\<close>
                          IxHOM_BA.resid
                          \<open>RTS.Pack \<one> (Hom (Dom t) A)\<close>
                          \<open>RTS.Unpack \<one> (Hom (Dom t) A)\<close>
            using assms t arr_char RTS.ide_one
                  RTS.inverse_simulations_Pack_Unpack [of \<one> "Hom (Dom t) A"]
            by simp
          have "?a \<star> t \<noteq> Null"
            using a t arr_hcomp null_char arr_char by blast
          moreover have "t \<noteq> Null"
            using t null_char arr_char by blast
          moreover have "Dom t = Dom (hcomp ?a t)"
            using a t hcomp_def by fastforce
          moreover have "Cod t = Cod (hcomp ?a t)"
            using a t hcomp_def by fastforce
          moreover have "Trn t = Trn (hcomp ?a t)"
          proof -
            have "Trn (?a \<star> t) =
                  RTS.Map (Comp (Dom t) A A)
                    (RTS.Pack (Hom A A) (Hom (Dom t) A)
                       (RTS.Map (Id A) RTS.One.the_arr, Trn t))"
              using a t hcomp_def by simp
            also have "... =
                  (RTS.Map (Comp (Dom t) A A) \<circ>
                     (RTS.Pack (Hom A A) (Hom (Dom t) A) \<circ>
                        Id_AxHOM_BA.map))
                     (RTS.One.the_arr, Trn t)"
              using assms t arr_char RTS.Map_ide Id_AxHOM_BA.map_simp
                    Id_A.preserves_reflects_arr RTS.ide_one a
              by auto
            also have "... =
                  (RTS.Map (Comp (Dom t) A A) \<circ>
                     (RTS.Map (Id A \<otimes> Hom (Dom t) A) \<circ>
                        RTS.Pack \<one> (Hom (Dom t) A)))
                     (RTS.One.the_arr, Trn t)"
            proof -
              have "RTS.Map (Id A \<otimes> Hom (Dom t) A) \<circ>
                      RTS.Pack \<one> (Hom (Dom t) A) =
                    (RTS.Pack (Hom A A) (Hom (Dom t) A) \<circ>
                       Id_AxHOM_BA.map \<circ>
                         RTS.Unpack \<one> (Hom (Dom t) A)) \<circ>
                      RTS.Pack \<one> (Hom (Dom t) A)"
                by (metis (no_types, lifting) HOM_BA.a Id_in_hom RTS.Map_prod
                    RTS.ide_char RTS.ide_one RTS.in_homE RTS.unity_agreement
                    assms ide_Hom)
              also have "... =
                    (RTS.Pack (Hom A A) (Hom (Dom t) A) \<circ>
                       Id_AxHOM_BA.map) \<circ>
                         (RTS.Unpack \<one> (Hom (Dom t) A) \<circ>
                            RTS.Pack \<one> (Hom (Dom t) A))"
                by auto
              also have "... = (RTS.Pack (Hom A A) (Hom (Dom t) A) \<circ>
                                  Id_AxHOM_BA.map) \<circ>
                                    I IxHOM_BA.resid"
              proof -
                have "RTS.Unpack \<one> (Hom (Dom t) A) \<circ>
                        RTS.Pack \<one> (Hom (Dom t) A) =
                      I IxHOM_BA.resid"
                  using PU.inv by fastforce
                thus ?thesis by simp
              qed
              also have "... = RTS.Pack (Hom A A) (Hom (Dom t) A) \<circ>
                                  (Id_AxHOM_BA.map \<circ> I IxHOM_BA.resid)"
                by auto
              also have "... = RTS.Pack (Hom A A) (Hom (Dom t) A) \<circ>
                                 Id_AxHOM_BA.map"
                using comp_simulation_identity
                        [of "IxHOM_BA.resid" "Id_AxHOM_BA.B1xB0.resid"
                            "Id_AxHOM_BA.map"]
                      Id_AxHOM_BA.simulation_axioms
                by auto
              finally have "RTS.Map (Id A \<otimes> Hom (Dom t) A) \<circ>
                              RTS.Pack \<one> (Hom (Dom t) A) =
                            RTS.Pack (Hom A A) (Hom (Dom t) A) \<circ> Id_AxHOM_BA.map"
                by blast
              thus ?thesis by simp
            qed
            also have "... =
                  ((RTS.Map (Comp (Dom t) A A) \<circ>
                      RTS.Map (Id A \<otimes> Hom (Dom t) A)) \<circ>
                        RTS.Pack \<one> (Hom (Dom t) A))
                     (RTS.One.the_arr, Trn t)"
              by auto
            also have "... =
                  (RTS.Map (Comp (Dom t) A A \<cdot> (Id A \<otimes> Hom (Dom t) A)) \<circ>
                     RTS.Pack \<one> (Hom (Dom t) A))
                     (RTS.One.the_arr, Trn t)"
              using assms t Comp_Id_Hom HOM_BA.a
                    RTS.Map_comp
                      [of "Comp (Dom t) A A" "Id A \<otimes> Hom (Dom t) A"]
              by auto
            also have "... = (RTS.Map \<l>[Hom (Dom t) A] \<circ>
                                RTS.Pack \<one> (Hom (Dom t) A))
                                (RTS.One.the_arr, Trn t)"
              using assms t arr_char Comp_Id_Hom
              by (simp add: RTS.lunit_agreement)
            also have "... = (IxHOM_BA.P\<^sub>0 \<circ>
                                RTS.Unpack RTS.one (Hom (Dom t) A) \<circ>
                                RTS.Pack \<one> (Hom (Dom t) A))
                                (RTS.One.the_arr, Trn t)"
              using assms t arr_char RTS.Map_lunit RTS.ide_one by auto
            also have "... = (IxHOM_BA.P\<^sub>0 \<circ>
                               (RTS.Unpack \<one> (Hom (Dom t) A) \<circ>
                                  RTS.Pack \<one> (Hom (Dom t) A)))
                               (RTS.One.the_arr, Trn t)"
              by auto
            also have "... = IxHOM_BA.P\<^sub>0 (RTS.One.the_arr, Trn t)"
              using assms t arr_char PU.inv IxHOM_BA.P\<^sub>0.simulation_axioms
                    comp_simulation_identity
                      [of "IxHOM_BA.resid" _ "IxHOM_BA.P\<^sub>0"]
              by simp
            also have "... = Trn t"
              using t arr_char IxHOM_BA.P\<^sub>0_def IxHOM_BA.arr_char
                    Id_A.preserves_reflects_arr RTS.ide_one a
              by auto
            finally show ?thesis by auto
          qed
          ultimately show ?thesis
            apply (cases t)
             apply auto[1]
            by (metis Cod.simps(1) Dom.simps(1) Trn.elims)
        qed
      qed
    qed

    lemma H_ide_is_V_ide:
    assumes "H.ide a"
    shows "V.ide a"
    proof -
      have 1: "V.arr a \<and> a = mkobj (Dom a)"
        by (metis assms Cod.simps(1) H_ide_char Id_yields_horiz_ide
            horizontal_unit_def arr_char)
      interpret HOM_AA: hom_rts arr_type Obj Hom Id Comp \<open>Dom a\<close> \<open>Dom a\<close>
        using assms 1 arr_char by unfold_locales simp
      interpret Id_A: simulation \<open>RTS.Dom \<one>\<close> \<open>HOM\<^sub>E\<^sub>C (Dom a) (Dom a)\<close>
                        \<open>RTS.Map (Id (Dom a))\<close>
        using 1 arr_char Id_in_hom RTS.arrD(3) RTS.ide_one by force
      have "V.ide (MkArr (Dom a) (Dom a)
                     (RTS.Map (Id (Dom a)) RTS.One.the_arr))"
      proof -
        have "Trn a = RTS.Map (Id (Dom a)) RTS.One.the_arr"
          using 1 by (metis Trn.simps(1))
        moreover have 2: "HOM_AA.ide ..."
          using Id_A.preserves_ide RTS.One.ide_char\<^sub>1\<^sub>R\<^sub>T\<^sub>S RTS.ide_one by force
        ultimately show ?thesis
          by (metis 1 Cod.simps(1) arr_char ide_char)
      qed
      thus "V.ide a"
        using 1 ide_char by metis
    qed

    lemma H_domains_char:
    shows "H.domains t = {a. V.arr t \<and> a = mkobj (Dom t)}"
    proof
      show "{a. V.arr t \<and> a = mkobj (Dom t)} \<subseteq> H.domains t"
      proof
        fix a
        assume a: "a \<in> {a. V.arr t \<and> a = mkobj (Dom t)}"
        have "H.ide a"
          using a arr_char Id_yields_horiz_ide by force
        thus "a \<in> H.domains t"
          using a H.domains_def H.ide_def H_composable_char H_null_char
          by force
      qed
      show "H.domains t \<subseteq> {a. V.arr t \<and> a = mkobj (Dom t)}"
      proof
        fix a
        assume a: "a \<in> H.domains t"
        have 1: "H.ide a \<and> hcomp t a \<noteq> H.null"
          using a H.domains_def by blast
        have "a = mkobj (Dom t)"
          using a 1 H.ide_def
          by (metis (no_types, lifting) Dom.simps(1) H_composable_char
              H_null_char Id_yields_horiz_ide arr_char)
        moreover have "V.arr t"
          using 1 hcomp_def null_char H_null_char by metis
        ultimately show "a \<in> {a. V.arr t \<and> a = mkobj (Dom t)}"
          by blast
      qed
    qed

    lemma H_codomains_char:
    shows "H.codomains t = {a. V.arr t \<and> a = mkobj (Cod t)}"
    proof
      show "{a. V.arr t \<and> a = mkobj (Cod t)} \<subseteq> H.codomains t"
      proof
        fix a
        assume a: "a \<in> {a. V.arr t \<and> a = mkobj (Cod t)}"
        have "H.ide a"
          using a arr_char Id_yields_horiz_ide by force
        thus "a \<in> H.codomains t"
          using a H.codomains_def H.ide_def H_composable_char H_null_char
          by force
      qed
      show "H.codomains t \<subseteq> {a. V.arr t \<and> a = mkobj (Cod t)}"
      proof
        fix a
        assume a: "a \<in> H.codomains t"
        have 1: "H.ide a \<and> hcomp a t \<noteq> H.null"
          using a H.codomains_def by blast
        have "a = mkobj (Cod t)"
          using a 1 H.ide_def
          by (metis (no_types, lifting) Cod.simps(1) H_composable_char
              H_null_char Id_yields_horiz_ide arr_char)
        moreover have "V.arr t"
          using 1 hcomp_def null_char H_null_char by metis
        ultimately show "a \<in> {a. V.arr t \<and> a = mkobj (Cod t)}"
          by blast
      qed
    qed

    lemma H_arr_char:
    shows "H.arr t \<longleftrightarrow> t \<noteq> Null \<and> Dom t \<in> Obj \<and> Cod t \<in> Obj \<and>
                       residuation.arr (HOM\<^sub>E\<^sub>C (Dom t) (Cod t)) (Trn t)"
    proof
      assume t: "H.arr t"
      interpret HOM: hom_rts arr_type Obj Hom Id Comp \<open>Dom t\<close> \<open>Cod t\<close>
        using t
        by unfold_locales
           (auto simp add: H.arr_def H_codomains_char H_domains_char arr_char)
      show "t \<noteq> Null \<and> Dom t \<in> Obj \<and> Cod t \<in> Obj \<and> HOM.arr (Trn t)"
        using t H.arr_def H_codomains_char H_domains_char arr_char by auto
      next
      assume t: "t \<noteq> Null \<and> Dom t \<in> Obj \<and> Cod t \<in> Obj \<and>
                 residuation.arr (HOM\<^sub>E\<^sub>C (Dom t) (Cod t)) (Trn t)"
      have "V.arr t"
        using t arr_char by blast
      thus "H.arr t"
        using t H.arr_def H_codomains_char H_domains_char arr_char
              Id_yields_horiz_ide
        by blast
    qed

    lemma H_seq_char:
    shows "H.seq t u \<longleftrightarrow> V.arr t \<and> V.arr u \<and> Dom t = Cod u"
      by (metis H_arr_char H_composable_char arr_char arr_hcomp null_char)

    sublocale H: category hcomp
    proof
      show "\<And>t u. hcomp t u \<noteq> H.null \<Longrightarrow> H.seq t u"
        using hcomp_def H_seq_char H_null_char null_char
        by auto argo+
      show "\<And>t. (H.domains t \<noteq> {}) = (H.codomains t \<noteq> {})"
        by (simp add: H_codomains_char H_domains_char)
      show "\<And>h g f. \<lbrakk>H.seq h g; H.seq (h \<star> g) f\<rbrakk> \<Longrightarrow> H.seq g f"
        using H_seq_char
        by (metis Dom.simps(1) hcomp_def)
      show "\<And>h g f. \<lbrakk>H.seq h (g \<star> f); H.seq g f\<rbrakk> \<Longrightarrow> H.seq h g"
        using H_seq_char
        by (metis Cod.simps(1) hcomp_def)
      show "\<And>g f h. \<lbrakk>H.seq g f; H.seq h g\<rbrakk> \<Longrightarrow> H.seq (h \<star> g) f"
        using H_seq_char
        by (metis Dom.simps(1) arr_hcomp hcomp_def)
      show "\<And>t u v. \<lbrakk>H.seq u v; H.seq t u\<rbrakk> \<Longrightarrow> (t \<star> u) \<star> v = t \<star> u \<star> v"
      proof (intro arr_eqI)
        fix t u v
        assume tu: "H.seq t u" and uv: "H.seq u v"
        show "(t \<star> u) \<star> v \<noteq> V.null"
          using tu uv arr_hcomp H_seq_char H_composable_char null_char by auto
        show "t \<star> u \<star> v \<noteq> V.null"
          using tu uv arr_hcomp H_seq_char H_composable_char null_char by auto
        show "Dom ((t \<star> u) \<star> v) = Dom (t \<star> u \<star> v)"
          using tu uv arr_hcomp H_seq_char H_composable_char null_char by simp
        show "Cod ((t \<star> u) \<star> v) = Cod (t \<star> u \<star> v)"
          using tu uv arr_hcomp H_seq_char H_composable_char null_char by simp
        show "Trn ((t \<star> u) \<star> v) = Trn (t \<star> u \<star> v)"
        proof -
          let ?A = "Dom v" and ?B = "Cod v" and ?C = "Cod u" and ?D = "Cod t"
          have A: "?A \<in> Obj" and B: "?B \<in> Obj" and C: "?C \<in> Obj" and D: "?D \<in> Obj"
            using tu uv arr_char arr_char [of u] arr_char [of v] H_seq_char by blast+
          interpret AB: hom_rts arr_type Obj Hom Id Comp ?A ?B
            using A B by unfold_locales
          interpret BC: hom_rts arr_type Obj Hom Id Comp ?B ?C
            using B C by unfold_locales
          interpret CD: hom_rts arr_type Obj Hom Id Comp ?C ?D
            using C D by unfold_locales
          interpret CDxBC: product_rts \<open>HOM\<^sub>E\<^sub>C ?C ?D\<close> \<open>HOM\<^sub>E\<^sub>C ?B ?C\<close> ..
          interpret BCxAB: product_rts \<open>HOM\<^sub>E\<^sub>C ?B ?C\<close> \<open>HOM\<^sub>E\<^sub>C ?A ?B\<close> ..
          interpret CDxBC_x_AB: product_rts CDxBC.resid \<open>HOM\<^sub>E\<^sub>C ?A ?B\<close> ..
          interpret CD_x_BCxAB: product_rts \<open>HOM\<^sub>E\<^sub>C ?C ?D\<close> BCxAB.resid ..
          interpret I_AB: simulation
                            \<open>HOM\<^sub>E\<^sub>C ?A ?B\<close> \<open>HOM\<^sub>E\<^sub>C ?A ?B\<close>
                            \<open>RTS.Map (Hom ?A ?B)\<close>
            using A B by (metis RTS.arrD(3) RTS.ideD(1-3) ide_Hom)
          interpret I_BC: simulation
                            \<open>HOM\<^sub>E\<^sub>C ?B ?C\<close> \<open>HOM\<^sub>E\<^sub>C ?B ?C\<close>
                            \<open>RTS.Map (Hom ?B ?C)\<close>
            using B C by (metis RTS.arrD(3) RTS.ideD(1-3) ide_Hom)
          interpret I_CD: simulation
                            \<open>HOM\<^sub>E\<^sub>C ?C ?D\<close> \<open>HOM\<^sub>E\<^sub>C ?C ?D\<close>
                            \<open>RTS.Map (Hom ?C ?D)\<close>
            using C D by (metis RTS.arrD(3) RTS.ideD(1-3) ide_Hom)
          interpret I_CDxI_BC: product_simulation
                                 \<open>HOM\<^sub>E\<^sub>C ?C ?D\<close> \<open>HOM\<^sub>E\<^sub>C ?B ?C\<close>
                                 \<open>HOM\<^sub>E\<^sub>C ?C ?D\<close> \<open>HOM\<^sub>E\<^sub>C ?B ?C\<close>
                                 \<open>RTS.Map (Hom ?C ?D)\<close> \<open>RTS.Map (Hom ?B ?C)\<close>
            ..
          interpret PU_BC_AB: inverse_simulations
                                \<open>RTS.Dom (Hom ?B ?C \<otimes> Hom ?A ?B)\<close>
                                BCxAB.resid
                                \<open>RTS.Pack (Hom ?B ?C) (Hom ?A ?B)\<close>
                                \<open>RTS.Unpack (Hom ?B ?C) (Hom ?A ?B)\<close>
            using A B C D RTS.inverse_simulations_Pack_Unpack by simp
          interpret PU_CD_BC: inverse_simulations
                                \<open>RTS.Dom (Hom ?C ?D \<otimes> Hom ?B ?C)\<close>
                                CDxBC.resid
                                \<open>RTS.Pack (Hom ?C ?D) (Hom ?B ?C)\<close>
                                \<open>RTS.Unpack (Hom ?C ?D) (Hom ?B ?C)\<close>
            using A B C D RTS.inverse_simulations_Pack_Unpack by simp
          interpret bcxab: extensional_rts \<open>RTS.Dom (Hom ?B ?C \<otimes> Hom ?A ?B)\<close>
            using A B C D RTS.arrD
                  RTS.ide_char [of "Hom ?B ?C \<otimes> Hom ?A ?B"]
            by blast
          interpret CD_x_bcxab: product_rts
                                  \<open>HOM\<^sub>E\<^sub>C ?C ?D\<close>
                                  \<open>RTS.Dom (Hom ?B ?C \<otimes> Hom ?A ?B)\<close>
             ..
          interpret cdxbc: extensional_rts \<open>RTS.Dom (Hom ?C ?D \<otimes> Hom ?B ?C)\<close>
            using A B C D RTS.arrD
                  RTS.ide_char [of "Hom ?C ?D \<otimes> Hom ?B ?C"]
            by blast
          interpret cdxbc_x_AB: product_rts
                                  \<open>RTS.Dom (Hom ?C ?D \<otimes> Hom ?B ?C)\<close>
                                  \<open>HOM\<^sub>E\<^sub>C ?A ?B\<close>
            ..
          interpret PU_cdxbc_x_AB: inverse_simulations
                                \<open>RTS.Dom ((Hom ?C ?D \<otimes> Hom ?B ?C) \<otimes> Hom ?A ?B)\<close>
                                cdxbc_x_AB.resid
                                \<open>RTS.Pack (Hom ?C ?D \<otimes> Hom ?B ?C) (Hom ?A ?B)\<close>
                                \<open>RTS.Unpack
                                   (Hom ?C ?D \<otimes> Hom ?B ?C) (Hom ?A ?B)\<close>
            using A B C D RTS.inverse_simulations_Pack_Unpack by auto
          interpret PU_CD_x_bcxab: inverse_simulations
                                      \<open>RTS.Dom
                                         (Hom ?C ?D \<otimes> Hom ?B ?C \<otimes> Hom ?A ?B)\<close>
                                      CD_x_bcxab.resid
                                      \<open>RTS.Pack
                                         (Hom ?C ?D) (Hom ?B ?C \<otimes> Hom ?A ?B)\<close>
                                      \<open>RTS.Unpack
                                         (Hom ?C ?D) (Hom ?B ?C \<otimes> Hom ?A ?B)\<close>
            using A B C D RTS.inverse_simulations_Pack_Unpack by auto
          interpret I_AB: identity_simulation \<open>HOM\<^sub>E\<^sub>C ?A ?B\<close> ..
          interpret U_CD_BC_x_I_AB: product_simulation
                                      \<open>RTS.Dom (Hom ?C ?D \<otimes> Hom ?B ?C)\<close>
                                         \<open>HOM\<^sub>E\<^sub>C ?A ?B\<close>
                                      CDxBC.resid \<open>HOM\<^sub>E\<^sub>C ?A ?B\<close>
                                      \<open>RTS.Unpack (Hom ?C ?D) (Hom ?B ?C)\<close>
                                      \<open>I (HOM\<^sub>E\<^sub>C ?A ?B)\<close>
            ..
          interpret C_CD_BC: simulation
                               \<open>RTS.Dom (Hom ?C ?D \<otimes> Hom ?B ?C)\<close>
                               \<open>HOM\<^sub>E\<^sub>C ?B ?D\<close>
                               \<open>RTS.Map (Comp ?B ?C ?D)\<close>
            using B C D Comp_in_hom [of ?B ?C ?D] arr_char
            by (metis (no_types, lifting) RTS.arrD(3) RTS.ideD(2) RTS.ide_prod
                RTS.in_homE ide_Hom prod.sel(1-2))
          interpret C_CD_BC_x_I_AB: product_simulation
                                      \<open>RTS.Dom (Hom ?C ?D \<otimes> Hom ?B ?C)\<close>
                                      \<open>HOM\<^sub>E\<^sub>C ?A ?B\<close>
                                      \<open>HOM\<^sub>E\<^sub>C ?B ?D\<close> \<open>HOM\<^sub>E\<^sub>C ?A ?B\<close>
                                      \<open>RTS.Map (Comp ?B ?C ?D)\<close>
                                      \<open>RTS.Map (Hom ?A ?B)\<close>
             ..
          interpret I_CD: identity_simulation \<open>HOM\<^sub>E\<^sub>C ?C ?D\<close> ..
          interpret I_CD_x_P_BC_AB: product_simulation
                                      \<open>HOM\<^sub>E\<^sub>C ?C ?D\<close> BCxAB.resid
                                      \<open>HOM\<^sub>E\<^sub>C ?C ?D\<close>
                                      \<open>RTS.Dom (Hom ?B ?C \<otimes> Hom ?A ?B)\<close>
                                      \<open>I (HOM\<^sub>E\<^sub>C ?C ?D)\<close>
                                      \<open>RTS.Pack (Hom ?B ?C) (Hom ?A ?B)\<close>
            ..
          interpret C_BC_AB: simulation
                               \<open>RTS.Dom (Hom ?B ?C \<otimes> Hom ?A ?B)\<close>
                               \<open>HOM\<^sub>E\<^sub>C ?A ?C\<close>
                               \<open>RTS.Map (Comp ?A ?B ?C)\<close>
            using A B C Comp_in_hom [of ?A ?B ?C] arr_char
            by (metis (no_types, lifting) RTS.arrD(3) RTS.ideD(2) RTS.ide_prod
                RTS.in_homE ide_Hom prod.sel(1) prod.sel(2))
          interpret I_CD_x_Comp_ABC: product_simulation
                                       \<open>HOM\<^sub>E\<^sub>C ?C ?D\<close>
                                       \<open>RTS.Dom (Hom ?B ?C \<otimes> Hom ?A ?B)\<close>
                                       \<open>HOM\<^sub>E\<^sub>C ?C ?D\<close> \<open>HOM\<^sub>E\<^sub>C ?A ?C\<close>
                                       \<open>RTS.Map (Hom ?C ?D)\<close>
                                       \<open>RTS.Map (Comp ?A ?B ?C)\<close>
            ..
          have "Trn ((t \<star> u) \<star> v) =
                (RTS.Map (Comp ?A ?B ?D)
                  (RTS.Pack (Hom ?B ?D) (Hom ?A ?B)
                    (RTS.Map (Comp ?B ?C ?D)
                      (RTS.Pack (Hom ?C ?D) (Hom ?B ?C) (Trn t, Trn u)),
                     Trn v)))"
            using tu uv H_seq_char \<open>(t \<star> u) \<star> v \<noteq> V.null\<close> hcomp_def by auto
          also have "... =
                RTS.Map (Comp ?A ?B ?D)
                  (RTS.Pack (Hom ?B ?D) (Hom ?A ?B)
                    (RTS.Map (Comp ?B ?C ?D)
                       (RTS.Pack (Hom ?C ?D) (Hom ?B ?C) (Trn t, Trn u)),
                     I (HOM\<^sub>E\<^sub>C ?A ?B) (Trn v)))"
            using H_seq_char arr_char uv by simp
          also have "... =
                RTS.Map (Comp ?A ?B ?D)
                  ((RTS.Pack (Hom ?B ?D) (Hom ?A ?B) \<circ> C_CD_BC_x_I_AB.map)
                      (RTS.Pack (Hom ?C ?D) (Hom ?B ?C) (Trn t, Trn u), Trn v))"
            using A B C D RTS.Map_ide C_CD_BC_x_I_AB.map_simp H_seq_char
                  PU_CD_BC.F.preserves_reflects_arr arr_char tu uv
            by force
          also have "... =
                RTS.Map (Comp ?A ?B ?D)
                  ((RTS.Map (Comp ?B ?C ?D \<otimes> Hom ?A ?B) \<circ>
                      RTS.Pack (Hom ?C ?D \<otimes> Hom ?B ?C) (Hom ?A ?B))
                      (RTS.Pack (Hom ?C ?D) (Hom ?B ?C) (Trn t, Trn u), Trn v))"
          proof -
            have "RTS.Map (Comp ?B ?C ?D \<otimes> Hom ?A ?B) \<circ>
                     RTS.Pack
                       (RTS.prod (Hom ?C ?D) (Hom ?B ?C)) (Hom ?A ?B) =
                  RTS.Pack (Hom ?B ?D) (Hom ?A ?B) \<circ> C_CD_BC_x_I_AB.map \<circ>
                      (RTS.Unpack (Hom ?C ?D \<otimes> Hom ?B ?C) (Hom ?A ?B) \<circ>
                         RTS.Pack (Hom ?C ?D \<otimes> Hom ?B ?C) (Hom ?A ?B))"
              using A B C D Comp_in_hom [of ?B ?C ?D]
                    RTS.Map_prod [of "Comp ?B ?C ?D" "Hom ?A ?B"]
              by fastforce
            also have "... =
                  RTS.Pack (Hom ?B ?D) (Hom ?A ?B) \<circ>
                    (C_CD_BC_x_I_AB.map \<circ> I cdxbc_x_AB.resid)"
              using PU_cdxbc_x_AB.inv
              by auto
            also have "... = RTS.Pack (Hom ?B ?D) (Hom ?A ?B) \<circ>
                               C_CD_BC_x_I_AB.map"
              using comp_simulation_identity
                      [of cdxbc_x_AB.resid C_CD_BC_x_I_AB.B1xB0.resid
                          C_CD_BC_x_I_AB.map]
                    C_CD_BC_x_I_AB.simulation_axioms
              by auto
            finally have "RTS.Map (Comp ?B ?C ?D \<otimes> Hom ?A ?B) \<circ>
                            RTS.Pack (Hom ?C ?D \<otimes> Hom ?B ?C) (Hom ?A ?B) =
                          RTS.Pack (Hom ?B ?D) (Hom ?A ?B) \<circ> C_CD_BC_x_I_AB.map"
              by blast
            thus ?thesis by simp
          qed
          also have "... =
                ((RTS.Map (Comp ?A ?B ?D) \<circ>
                    RTS.Map (Comp ?B ?C ?D \<otimes> Hom ?A ?B)) \<circ>
                      RTS.Pack (Hom ?C ?D \<otimes> Hom ?B ?C) (Hom ?A ?B))
                        (RTS.Pack (Hom ?C ?D) (Hom ?B ?C) (Trn t, Trn u), Trn v)"
            by auto
          also have "... =
                (RTS.Map (Comp ?A ?B ?D \<cdot> (Comp ?B ?C ?D \<otimes> Hom ?A ?B)) \<circ>
                    RTS.Pack (Hom ?C ?D \<otimes> Hom ?B ?C) (Hom ?A ?B))
                      (RTS.Pack (Hom ?C ?D) (Hom ?B ?C) (Trn t, Trn u), Trn v)"
          proof -
            have "RTS.seq (Comp ?A ?B ?D) (Comp ?B ?C ?D \<otimes> Hom ?A ?B)"
              using A B C D Comp_in_hom
              apply (intro RTS.seqI)
                apply auto[3]
              by (metis RTS.ide_char RTS.in_homE RTS.prod_simps(1,3) ide_Hom)+
            thus ?thesis
              using RTS.Map_comp
                      [of "Comp ?A ?B ?D" "Comp ?B ?C ?D \<otimes> Hom ?A ?B"]
              by argo
          qed
          also have "... =
                (RTS.Map (Comp ?A ?C ?D \<cdot> (Hom ?C ?D \<otimes> Comp ?A ?B ?C) \<cdot>
                            \<a>[Hom ?C ?D, Hom ?B ?C, Hom ?A ?B]) \<circ>
                    RTS.Pack (Hom ?C ?D \<otimes> Hom ?B ?C) (Hom ?A ?B))
                      (RTS.Pack (Hom ?C ?D) (Hom ?B ?C) (Trn t, Trn u), Trn v)"
            using A B C D Comp_assoc RTS.assoc_agreement by auto
          also have "... =
                ((RTS.Map (Comp ?A ?C ?D) \<circ>
                    RTS.Map ((Hom ?C ?D \<otimes> Comp ?A ?B ?C) \<cdot>
                               \<a>[Hom ?C ?D, Hom ?B ?C, Hom ?A ?B])) \<circ>
                    RTS.Pack (Hom ?C ?D \<otimes> Hom ?B ?C) (Hom ?A ?B))
                      (RTS.Pack (Hom ?C ?D) (Hom ?B ?C) (Trn t, Trn u), Trn v)"
          proof -
            have "RTS.seq
                    (Comp ?A ?C ?D)
                    ((Hom ?C ?D \<otimes> Comp ?A ?B ?C) \<cdot>
                        \<a>[Hom ?C ?D, Hom ?B ?C, Hom ?A ?B])"
              using A B C D
                    Comp_in_hom [of ?A ?C ?D] Comp_in_hom [of ?A ?B ?C]
                    RTS.assoc_in_hom
              apply (intro RTS.seqI)
                  apply auto[4]
              by fastforce
            thus ?thesis
              using RTS.Map_comp
                      [of "Comp ?A ?C ?D"
                          "(Hom ?C ?D \<otimes> Comp ?A ?B ?C) \<cdot>
                             \<a>[Hom ?C ?D, Hom ?B ?C, Hom ?A ?B]"]
              by argo
          qed
          also have "... =
                ((RTS.Map (Comp ?A ?C ?D) \<circ>
                   (RTS.Map (Hom ?C ?D \<otimes> Comp ?A ?B ?C) \<circ>
                      RTS.Map
                        (RTS.assoc (Hom ?C ?D) (Hom ?B ?C) (Hom ?A ?B)))) \<circ>
                    RTS.Pack (Hom ?C ?D \<otimes> Hom ?B ?C) (Hom ?A ?B))
                      (RTS.Pack (Hom ?C ?D) (Hom ?B ?C) (Trn t, Trn u), Trn v)"
          proof -
            have "RTS.seq (Hom ?C ?D \<otimes> Comp ?A ?B ?C)
                    \<a>[Hom (Cod u) (Cod t), Hom (Cod v) (Cod u),
                      Hom (Dom v) (Cod v)]"
              using A B C D Comp_in_hom [of ?A ?B ?C] RTS.assoc_simps(1,3)
                    RTS.arrI
              by (intro RTS.seqI) auto
            thus ?thesis
              using RTS.Map_comp
                      [of "Hom ?C ?D \<otimes> Comp ?A ?B ?C"
                          "RTS.assoc (Hom ?C ?D) (Hom ?B ?C) (Hom ?A ?B)"]
              by auto
          qed
          also have "... =
                (RTS.Map (Comp ?A ?C ?D) \<circ>
                   RTS.Map (Hom ?C ?D \<otimes> Comp ?A ?B ?C))
                   (RTS.Map (RTS.assoc (Hom ?C ?D) (Hom ?B ?C) (Hom ?A ?B))
                      (RTS.Pack (Hom ?C ?D \<otimes> Hom ?B ?C) (Hom ?A ?B)
                         (RTS.Pack (Hom ?C ?D) (Hom ?B ?C) (Trn t, Trn u),
                          Trn v)))"
            using comp_assoc by simp
          also have "... =
                (RTS.Map (Comp ?A ?C ?D) \<circ>
                   RTS.Map (Hom ?C ?D \<otimes> Comp ?A ?B ?C))
                   ((RTS.Pack (Hom ?C ?D) (Hom ?B ?C \<otimes> Hom ?A ?B) \<circ>
                       I_CD_x_P_BC_AB.map \<circ>
                         ASSOC.map
                           (HOM\<^sub>E\<^sub>C ?C ?D) (HOM\<^sub>E\<^sub>C ?B ?C) (HOM\<^sub>E\<^sub>C ?A ?B) \<circ>
                           U_CD_BC_x_I_AB.map)
                       ((RTS.Unpack (Hom ?C ?D \<otimes> Hom ?B ?C) (Hom ?A ?B) \<circ>
                           RTS.Pack (Hom ?C ?D \<otimes> Hom ?B ?C) (Hom ?A ?B))
                           (RTS.Pack (Hom ?C ?D) (Hom ?B ?C) (Trn t, Trn u),
                            Trn v)))"
            using A B C D RTS.Map_assoc by simp
          also have "... =
                (RTS.Map (Comp ?A ?C ?D) \<circ>
                   RTS.Map (Hom ?C ?D \<otimes> Comp ?A ?B ?C))
                   ((RTS.Pack (Hom ?C ?D) (Hom ?B ?C \<otimes> Hom ?A ?B) \<circ>
                       I_CD_x_P_BC_AB.map \<circ>
                         ASSOC.map
                           (HOM\<^sub>E\<^sub>C ?C ?D) (HOM\<^sub>E\<^sub>C ?B ?C) (HOM\<^sub>E\<^sub>C ?A ?B))
                      (U_CD_BC_x_I_AB.map
                         (RTS.Pack (Hom ?C ?D) (Hom ?B ?C) (Trn t, Trn u),
                          Trn v)))"
          proof -
            have "RTS.Unpack (Hom ?C ?D \<otimes> Hom ?B ?C) (Hom ?A ?B) \<circ>
                    RTS.Pack (Hom ?C ?D \<otimes> Hom ?B ?C) (Hom ?A ?B) =
                  I cdxbc_x_AB.resid" 
              using A B C D PU_cdxbc_x_AB.inv by blast
            moreover have "I cdxbc_x_AB.resid
                             (RTS.Pack (Hom ?C ?D) (Hom ?B ?C)
                                (Trn t, Trn u), Trn v) =
                           (RTS.Pack (Hom ?C ?D) (Hom ?B ?C) (Trn t, Trn u),
                            Trn v)"
            proof -
              have "CDxBC.arr (Trn t, Trn u)"
                using tu uv arr_char [of t] arr_char [of u] H_seq_char by auto
              moreover have "AB.arr (Trn v)"
                using uv arr_char H_seq_char by simp
              ultimately have "cdxbc_x_AB.arr
                                 (RTS.Pack (Hom ?C ?D) (Hom ?B ?C) (Trn t, Trn u),
                                  Trn v)"
                using A B C D PU_CD_BC.F.preserves_reflects_arr by fastforce
              thus ?thesis by auto
            qed
            ultimately show ?thesis by simp
          qed
          also have "... =
                (RTS.Map (Comp ?A ?C ?D) \<circ>
                   RTS.Map (Hom ?C ?D \<otimes> Comp ?A ?B ?C))
                   ((RTS.Pack (Hom ?C ?D) (Hom ?B ?C \<otimes> Hom ?A ?B) \<circ>
                       I_CD_x_P_BC_AB.map \<circ>
                         ASSOC.map
                           (HOM\<^sub>E\<^sub>C ?C ?D) (HOM\<^sub>E\<^sub>C ?B ?C) (HOM\<^sub>E\<^sub>C ?A ?B))
                         ((RTS.Unpack (Hom ?C ?D) (Hom ?B ?C) \<circ>
                             RTS.Pack (Hom ?C ?D) (Hom ?B ?C))
                             (Trn t, Trn u),
                           Trn v))"
          proof -
            have "cdxbc_x_AB.arr
                    (RTS.Pack (Hom ?C ?D) (Hom ?B ?C) (Trn t, Trn u), Trn v)"
              using tu uv arr_char H_seq_char PU_CD_BC.F.preserves_reflects_arr
              by fastforce
            thus ?thesis
              using A B C D U_CD_BC_x_I_AB.map_simp by fastforce
          qed
          also have "... =
                (RTS.Map (Comp ?A ?C ?D) \<circ>
                   RTS.Map (Hom ?C ?D \<otimes> Comp ?A ?B ?C))
                   ((RTS.Pack (Hom ?C ?D) (Hom ?B ?C \<otimes> Hom ?A ?B) \<circ>
                       I_CD_x_P_BC_AB.map)
                       (ASSOC.map
                          (HOM\<^sub>E\<^sub>C ?C ?D) (HOM\<^sub>E\<^sub>C ?B ?C) (HOM\<^sub>E\<^sub>C ?A ?B)
                          ((Trn t, Trn u), Trn v)))"
            using tu uv arr_char H_seq_char PU_CD_BC.inv by fastforce
          also have "... =
                (RTS.Map (Comp ?A ?C ?D) \<circ>
                   RTS.Map (Hom ?C ?D \<otimes> Comp ?A ?B ?C))
                   ((RTS.Pack (Hom ?C ?D) (Hom ?B ?C \<otimes> Hom ?A ?B) \<circ>
                       I_CD_x_P_BC_AB.map)
                       (Trn t, Trn u, Trn v))"
          proof -
            interpret A: ASSOC
                           \<open>HOM\<^sub>E\<^sub>C ?C ?D\<close> \<open>HOM\<^sub>E\<^sub>C ?B ?C\<close> \<open>HOM\<^sub>E\<^sub>C ?A ?B\<close>
              ..
            have "CDxBC_x_AB.arr ((Trn t, Trn u), Trn v)"
              using tu uv arr_char H_seq_char by fastforce
            thus ?thesis
              using A.map_eq by simp
          qed
          also have "... =
                (RTS.Map (Comp ?A ?C ?D)
                  ((RTS.Map (Hom ?C ?D \<otimes> Comp ?A ?B ?C) \<circ>
                     RTS.Pack (Hom ?C ?D) (Hom ?B ?C \<otimes> Hom ?A ?B))
                      (Trn t, RTS.Pack (Hom ?B ?C) (Hom ?A ?B) (Trn u, Trn v))))"
            using tu uv arr_char H_seq_char by fastforce
          also have "... =
                RTS.Map (Comp ?A ?C ?D)
                  ((RTS.Pack (Hom ?C ?D) (Hom ?A ?C) \<circ> I_CD_x_Comp_ABC.map)
                      (Trn t, RTS.Pack (Hom ?B ?C) (Hom ?A ?B) (Trn u, Trn v)))"
          proof -
            have "RTS.Map (Hom ?C ?D \<otimes> Comp ?A ?B ?C) \<circ>
                    RTS.Pack (Hom ?C ?D) (Hom ?B ?C \<otimes> Hom ?A ?B) =
                  (RTS.Pack (Hom ?C ?D) (Hom ?A ?C) \<circ>
                     I_CD_x_Comp_ABC.map \<circ>
                     (RTS.Unpack (Hom ?C ?D) (Hom ?B ?C \<otimes> Hom ?A ?B) \<circ>
                        RTS.Pack (Hom ?C ?D) (Hom ?B ?C \<otimes> Hom ?A ?B)))"
              using A B C D RTS.Map_prod [of "Hom ?C ?D" "Comp ?A ?B ?C"]
                    Comp_in_hom [of ?A ?B ?C]
              by fastforce
            also have "... =
                  (RTS.Pack (Hom ?C ?D) (Hom ?A ?C) \<circ>
                     (I_CD_x_Comp_ABC.map \<circ> I CD_x_bcxab.resid))"
              using PU_CD_x_bcxab.inv by auto
            also have "... = RTS.Pack (Hom ?C ?D) (Hom ?A ?C) \<circ>
                               I_CD_x_Comp_ABC.map"
              using comp_simulation_identity
                      [of CD_x_bcxab.resid _ I_CD_x_Comp_ABC.map]
                    I_CD_x_Comp_ABC.simulation_axioms
              by simp
            finally have "RTS.Map (Hom ?C ?D \<otimes> Comp ?A ?B ?C) \<circ>
                            RTS.Pack (Hom ?C ?D) (Hom ?B ?C \<otimes> Hom ?A ?B) =
                          RTS.Pack (Hom ?C ?D) (Hom ?A ?C) \<circ> I_CD_x_Comp_ABC.map"
              by simp
            thus ?thesis by simp
          qed
          also have "... =
                RTS.Map (Comp ?A ?C ?D)
                  (RTS.Pack (Hom ?C ?D) (Hom ?A ?C)
                    (Trn t,
                     RTS.Map (Comp ?A ?B ?C)
                       (RTS.Pack (Hom ?B ?C) (Hom ?A ?B) (Trn u, Trn v))))"
            using A B C D tu uv arr_char H_seq_char RTS.Map_ide
                  I_CD_x_Comp_ABC.map_simp
                    [of "Trn t" "RTS.Pack (Hom ?B ?C) (Hom ?A ?B) (Trn u, Trn v)"]
            by fastforce
          also have "... = Trn (t \<star> u \<star> v)"
            using tu uv H_seq_char
            apply auto[1]
            using arr_hcomp hcomp_def by auto
          finally show "Trn ((t \<star> u) \<star> v) = Trn (t \<star> u \<star> v)"
            by blast
        qed
      qed
    qed

    lemma is_category:
    shows "category hcomp"
      ..

    lemma H_dom_char:
    shows "H.dom =
           (\<lambda>t. if H.arr t
                then MkArr (Dom t) (Dom t)
                       (RTS.Map (Id (Dom t)) RTS.One.the_arr)
                else V.null)"
      using H_domains_char H.dom_in_domains H.has_domain_iff_arr H.dom_def
            H_null_char
      by auto

    lemma H_dom_simp:
    assumes "V.arr t"
    shows "H.dom t = MkArr (Dom t) (Dom t)
                       (RTS.Map (Id (Dom t)) RTS.One.the_arr)"
      using assms arr_char H_arr_char H_dom_char by fastforce

    lemma H_cod_char:
    shows "H.cod =
           (\<lambda>t. if H.arr t
                then MkArr (Cod t) (Cod t)
                       (RTS.Map (Id (Cod t)) RTS.One.the_arr)
                else V.null)"
      using H_codomains_char H.cod_in_codomains H.has_codomain_iff_arr
            H.cod_def H_null_char
      by auto

    lemma H_cod_simp:
    assumes "V.arr t"
    shows "H.cod t = MkArr (Cod t) (Cod t)
                       (RTS.Map (Id (Cod t)) RTS.One.the_arr)"
      using assms arr_char H_arr_char H_cod_char by fastforce

    lemma con_implies_H_par:
    assumes "V.con t u"
    shows "H.par t u"
      using assms con_char V.con_implies_arr(1-2) H_arr_char
            H_dom_simp H_cod_simp
      by (simp add: arr_char con_implies_Par(1-2))

    lemma H_par_resid:
    assumes "V.con t u"
    shows "H.par t (resid t u)"
      using assms con_char V.con_implies_arr(1-2) H_arr_char
            H_dom_simp H_cod_simp
            Dom_resid Cod_resid arr_char V.arr_resid
      by (intro conjI) metis+

    lemma simulation_dom:
    shows "simulation resid resid H.dom"
      using H_dom_char arr_char H_arr_char con_char
      apply unfold_locales
        apply auto[1]
      apply (metis (no_types, lifting) Con_def H.arr_dom V.arrE)
      by (metis (no_types, lifting) H.ide_dom H_ide_is_V_ide H_par_resid
          V.ideE con_implies_H_par)

    lemma simulation_cod:
    shows "simulation resid resid H.cod"
      using H_cod_char arr_char H_arr_char con_char
      apply unfold_locales
        apply presburger
       apply (metis (no_types, lifting) H.arr_cod V.arr_def
           rts_category_of_enriched_category.ConE
           rts_category_of_enriched_category_axioms)
      by (metis (no_types, lifting) H.ide_cod H_ide_is_V_ide
          H_par_resid V.con_implies_arr(2) V.ideE con_implies_Par(2))

    sublocale dom: simulation resid resid H.dom
      using simulation_dom by blast
    sublocale cod: simulation resid resid H.cod
      using simulation_cod by blast
    sublocale RR: fibered_product_rts resid resid resid H.dom H.cod ..

    sublocale H: simulation RR.resid resid
                   \<open>\<lambda>t. if RR.arr t then fst t \<star> snd t else V.null\<close>
    proof
      let ?C = "\<lambda>t. if RR.arr t then fst t \<star> snd t else V.null"
      show "\<And>t. \<not> RR.arr t \<Longrightarrow> ?C t = V.null"
        by simp
      fix t u
      assume tu: "RR.con t u"
      have arr_t: "RR.arr t"
        using tu RR.con_implies_arr by blast
      have arr_u: "RR.arr u"
        using tu RR.con_implies_arr by blast
      have t: "V.arr (fst t) \<and> V.arr (snd t) \<and> Dom (fst t) = Cod (snd t)"
        by (metis H_cod_simp H_dom_simp RR.arr_char arr.inject arr_t)
      have u: "V.arr (fst u) \<and> V.arr (snd u) \<and> Dom (fst u) = Cod (snd u)"
        using H_cod_simp H_dom_simp RR.arr_char arr_u by auto
      let ?a = "Dom (snd t)" and ?b = "Cod (snd t)" and ?c = "Cod (fst t)"
      have a: "?a \<in> Obj" and b: "?b \<in> Obj" and c: "?c \<in> Obj"
        using tu RR.con_char RR.con_implies_arr ide_char arr_char by fast+
      interpret AB: hom_rts arr_type Obj Hom Id Comp ?a ?b
        using t u ide_char arr_char
        by unfold_locales auto
      interpret BC: hom_rts arr_type Obj Hom Id Comp ?b ?c
        using t u ide_char arr_char
        by unfold_locales auto
      interpret AC: hom_rts arr_type Obj Hom Id Comp ?a ?c
        using t u ide_char arr_char
        by unfold_locales auto
      interpret BCxAB: product_rts \<open>HOM\<^sub>E\<^sub>C ?b ?c\<close> \<open>HOM\<^sub>E\<^sub>C ?a ?b\<close> ..
      interpret bcxab: extensional_rts
                         \<open>RTS.Rts (RTS.dom (Hom ?b ?c \<otimes> Hom ?a ?b))\<close>
        using t u ide_char arr_char by auto
      have 1: "Dom (snd u) = ?a"
        using tu RR.con_char RR.arr_char RR.con_implies_arr RR.con_sym
              H_dom_simp H_cod_simp
        by (meson con_implies_Par(1))
      have 2: "Cod (fst u) = ?c"
        using tu RR.con_char RR.arr_char RR.con_implies_arr RR.con_sym
              H_dom_simp H_cod_simp
        by (meson con_implies_Par(2))
      have 3: "Cod (snd u) = ?b"
        using tu RR.con_char RR.arr_char RR.con_implies_arr RR.con_sym
              H_dom_simp H_cod_simp
        by (meson con_implies_Par(2))
      have 4: "BCxAB.con (Trn (fst t), Trn (snd t)) (Trn (fst u), Trn (snd u))"
        using tu RR.con_char BCxAB.con_char con_char t by auto

      interpret P: simulation BCxAB.resid
                     \<open>RTS.Rts (RTS.dom (Hom ?b ?c \<otimes> Hom ?a ?b))\<close> 
                     \<open>RTS.Pack (Hom ?b ?c) (Hom ?a ?b)\<close>
        using a b c RTS.simulation_Pack by auto
      have 5: "bcxab.con
                 (RTS.Pack (Hom ?b ?c) (Hom ?a ?b) (Trn (fst t), Trn (snd t)))
                 (RTS.Pack (Hom ?b ?c) (Hom ?a ?b) (Trn (fst u), Trn (snd u)))"
        using 4 P.preserves_con by simp
      interpret Comp: simulation
                        \<open>RTS.Rts (RTS.dom  (Hom ?b ?c \<otimes> Hom ?a ?b))\<close>
                        \<open>HOM\<^sub>E\<^sub>C ?a ?c\<close>
                        \<open>RTS.Map (Comp ?a ?b ?c)\<close>
        using a b c Comp_in_hom arr_char
        by (metis (no_types, lifting) RTS.arrD(3) RTS.ideD(2) RTS.ide_prod
            RTS.in_homE ide_Hom prod.sel(1-2))
      show con: "?C t \<frown> ?C u"
      proof -
        have "AC.con (RTS.Map (Comp ?a ?b ?c)
                        (RTS.Pack (Hom ?b ?c) (Hom ?a ?b)
                           (Trn (fst t), Trn (snd t))))
                     (RTS.Map (Comp ?a ?b ?c)
                        (RTS.Pack (Hom ?b ?c) (Hom ?a ?b)
                         (Trn (fst u), Trn (snd u))))"
          using 5 Comp.preserves_con by blast
        thus ?thesis
          using 1 2 3 AC.con_implies_arr(1-2) Con_def H_composable_char
                a arr_t arr_u c con_char null_char t u
          by auto
      qed
      show "?C (RR.resid t u) = resid (?C t) (?C u)"
      proof -
        have "resid (?C t) (?C u) =
              MkArr ?a ?c
                (RTS.Map (Comp ?a ?b ?c)
                  (RTS.Rts (RTS.dom (Hom ?b ?c \<otimes> Hom ?a ?b))
                     (RTS.Pack (Hom ?b ?c) (Hom ?a ?b) (Trn (fst t), Trn (snd t)))
                     (RTS.Pack (Hom ?b ?c) (Hom ?a ?b) (Trn (fst u), Trn (snd u)))))"
          using a b c t u arr_t arr_u 1 2 3 4 5 hcomp_def P.preserves_reflects_arr
                arr_char Comp.preserves_resid con con_char by force
        also have "... = ?C (RR.resid t u)"
          using tu t u a b c 1 2 3 4 RR.con_char RR.arr_resid hcomp_def
                RR.resid_def BCxAB.resid_def P.preserves_resid
          by auto
        finally show ?thesis by simp
      qed
    qed

    lemma simulation_hcomp:
    shows "simulation RR.resid resid
             (\<lambda>t. if RR.arr t then fst t \<star> snd t else V.null)"
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

    lemma null_coincidence [simp]:
    shows "H.null = V.null"
      using H_null_char by blast

    lemma arr_coincidence [simp]:
    shows "H.arr = V.arr"
      using H_arr_char arr_char by blast

    lemma dom_src [simp]:
    shows "H.dom (V.src t) = H.dom t"
      using H_dom_char H_arr_char arr_char null_char V.arr_src_iff_arr
      by auto

    lemma src_dom [simp]:
    shows "V.src (H.dom t) = H.dom t"
      using H_ide_is_V_ide V.src_def V.src_ide dom.extensional by auto

    lemma small_homs:
    shows "small (H.hom a b)"
    proof -
      have "\<not> H.ide a \<or> \<not> H.ide b \<Longrightarrow> ?thesis"
      proof -
        assume 1: "\<not> H.ide a \<or> \<not> H.ide b"
        have "H.hom a b = {}"
          using 1 H.ide_dom H.ide_cod by blast
        thus ?thesis by auto
      qed
      moreover have "\<lbrakk>H.ide a; H.ide b\<rbrakk> \<Longrightarrow> ?thesis"
      proof -
        assume a: "H.ide a" and b: "H.ide b"
        interpret Hom: hom_rts arr_type Obj Hom Id Comp \<open>Dom a\<close> \<open>Dom b\<close>
          using a b
          by (meson H.ideD(1) H_arr_char hom_rts.intro hom_rts_axioms.intro
              rts_enriched_category_axioms)
        have "bij_betw Trn (H.hom a b) (Collect Hom.arr)"
        proof (intro bij_betwI)
          show "Trn \<in> H.hom a b \<rightarrow> Collect Hom.arr"
            using a b H_ide_char H_arr_char ide_char arr_char
                  H_ide_is_V_ide
            by (auto simp add: H_dom_simp H_cod_simp)
          show "(\<lambda>t. MkArr (Dom a) (Dom b) t) \<in> Collect Hom.arr \<rightarrow> H.hom a b"
            using a b H.ideD(1-2) H_cod_simp H_dom_char Hom.a Hom.b
                  arr_MkArr arr_coincidence
            by auto
          show "\<And>x. x \<in> H.hom a b \<Longrightarrow> MkArr (Dom a) (Dom b) (Trn x) = x"
            by (metis CollectD H.ide_in_hom H.seqI' H_seq_char MkArr_Trn a b)
          show "\<And>y. y \<in> Collect Hom.arr \<Longrightarrow> Trn (MkArr (Dom a) (Dom b) y) = y"
            using a b by auto
        qed
        hence "inj_on Trn (H.hom a b) \<and> Collect Hom.arr = Trn ` H.hom a b"
          using bij_betw_imp_inj_on bij_betw_imp_surj_on by metis
        thus ?thesis
          using Hom.small small_image_iff by auto
      qed
      ultimately show ?thesis by blast
    qed

    text\<open>
      Note that the arrow type of the RTS-category given by the following is
      @{typ "('O, 'A) arr"}, where 'A is the type of the universe underlying the
      category RTS and 'O is the type of objects of the context RTS-enriched
      category.  If we start with an RTS-enriched category having object type 'O,
      then we construct an RTS-category having arrow type @{typ "('O, 'A) arr"},
      and then we try to go back to an RTS-enriched category, the hom-RTS's
      will have arrow type @{typ "('O, 'A) arr"}, not \<open>'A\<close> as required for them to
      determine objects of \<open>RTS\<close>.  So to show that the passage between RTS-categories
      and RTS-enriched categories is an equivalence, we will need to be able to
      reduce the type of the hom-RTS's from @{typ "('O, 'A) arr"} back to \<open>'A\<close>.
    \<close>

    sublocale rts_category resid hcomp
      using null_coincidence arr_coincidence small_homs
      by unfold_locales auto

    proposition is_rts_category:
    shows "rts_category resid hcomp"
      ..

  end

subsection "The Small Case"

  text\<open>
    Given an RTS-enriched category, the corresponding RTS-category \<open>R\<close> has arrows at
    a higher type than the arrow type \<open>'A\<close> of the base category \<open>RTS\<close>.  In particular,
    the arrow type for this category is \<open>('O, 'A) arr\<close>, where \<open>'O\<close> is the element
    type of \<open>Obj\<close>.  If we want to reconstruct the original RTS-enriched category up
    to isomorphism, then we need to be able to map this type back down to \<open>'A\<close>,
    so that we can obtain (via \<open>RTS.MkIde\<close>) an RTS \<open>R'\<close> with arrow type \<open>'A\<close>,
    which is isomorphic to the desired RTS-category \<open>R\<close>.
    For this to be possible, clearly we need the set \<open>Obj\<close> to be small.
    However, we also need a way to represent each element of \<open>Obj\<close> uniquely as an
    element of \<open>'A\<close>.  This would be true automatically if we knew that \<open>'A\<close> were
    large enough to embed all small sets, but we don't want to tie the definition
    of the category \<open>RTS\<close> itself to a particular definition of ``small''.  So, here we
    instead just directly assume the existence of an injection from \<open>Obj\<close> to \<open>'A\<close>.
  \<close>

  locale rts_category_of_small_enriched_category =
    rts_category_of_enriched_category arr_type Obj Hom Id Comp
  for arr_type :: "'A itself"
  and Obj :: "'O set"
  and Hom :: "'O \<Rightarrow> 'O \<Rightarrow> 'A rtscatx.arr"
  and Id :: "'O \<Rightarrow> 'A rtscatx.arr"
  and Comp :: "'O \<Rightarrow> 'O \<Rightarrow> 'O \<Rightarrow> 'A rtscatx.arr" +
  assumes small_Obj: "small Obj"
  and inj_Obj_to_arr: "\<exists>\<phi> :: 'O \<Rightarrow> 'A. inj_on \<phi> Obj"
  begin

     text\<open>
       We will use \<open>R\<close> to refer to the RTS constructed from the given enriched category.
     \<close>

     abbreviation R :: "('O, 'A) arr resid"
     where "R \<equiv> resid"

     text\<open>
       The locale assumptions are sufficient to allow us to uniquely encode each element
       of @{term "Collect arr \<union> {null}"} as single element of \<open>'A\<close>.
     \<close>

     lemma ex_arrow_injection:
     shows "\<exists>i :: ('O, 'A) arr \<Rightarrow> 'A. inj_on i (Collect arr \<union> {null})"
     proof -
       obtain \<phi> :: "'O \<Rightarrow> 'A" where \<phi>: "inj_on \<phi> Obj"
         using inj_Obj_to_arr by blast
       let ?p = "\<lambda>t. some_pair (some_pair (\<phi> (Dom t), \<phi> (Cod t)), Trn t)"
       have p: "inj_on ?p (Collect arr)"
         by (metis (mono_tags, lifting) CollectD \<phi> arr_char arr_eqI
             first_conv inj_onD inj_onI null_char second_conv)
       let ?i = "\<lambda>x. some_lift (if arr x then Some (?p x) else None)"
       have "inj_on ?i (Collect arr \<union> {null})"
       proof
         fix x y
         assume x: "x \<in> Collect arr \<union> {null}" and y: "y \<in> Collect arr \<union> {null}"
         assume eq: "?i x = ?i y"
         show "x = y"
           using x y eq p inj_some_lift injD inj_on_contraD by fastforce
       qed
       thus ?thesis by auto
     qed

     lemma bij_betw_Obj_horiz_ide:
     shows "bij_betw mkobj Obj (Collect H.ide)"
       using arr_char Id_yields_horiz_ide H_ide_char horizontal_unit_def
       apply (intro bij_betwI)
          apply auto[3]
       by (metis Dom.simps(1) mem_Collect_eq)

     lemma ex_isomorphic_image_rts:
     shows "\<exists>R' (UP :: 'A \<Rightarrow> ('O, 'A) arr) (DN :: ('O, 'A) arr \<Rightarrow> 'A).
               small_rts R' \<and> extensional_rts R' \<and> inverse_simulations R R' UP DN"
     proof -
       obtain i :: "('O, 'A) arr \<Rightarrow> 'A" where i: "inj_on i (Collect arr \<union> {null})"
         using ex_arrow_injection by blast
       interpret R': inj_image_rts i R
         using i by unfold_locales
       interpret R': extensional_rts R'.resid
         using V.extensional_rts_axioms R'.preserves_extensional_rts by blast
       interpret R': small_rts R'.resid
       proof -
         have "small (Collect arr)"
         proof -
           have "small ((Collect H.ide \<times> Collect H.ide) \<times>
                           (\<Union>x\<in>Collect H.ide \<times> Collect H.ide.
                                  H.hom (fst x) (snd x)))"
           proof -
             have "\<And>a b. \<lbrakk>H.ide a; H.ide b\<rbrakk> \<Longrightarrow> small (H.hom a b)"
               using small_homs by auto
             moreover have "small (Collect H.ide \<times> Collect H.ide)"
               using small_Obj bij_betw_Obj_horiz_ide
               by (metis (no_types, lifting) bij_betw_imp_surj_on replacement
                   small_Sigma)
             ultimately show ?thesis
               using small_homs by force
           qed
           moreover
           have "(\<lambda>t. ((H.dom t, H.cod t), t)) \<in>
                          Collect arr \<rightarrow>
                            ((Collect H.ide \<times> Collect H.ide) \<times>
                               (\<Union>x\<in>Collect H.ide \<times> Collect H.ide.
                                    H.hom (fst x) (snd x)))"
           proof
             fix t
             assume t: "t \<in> Collect arr"
             have "H.dom t \<in> Collect H.ide \<and> H.cod t \<in> Collect H.ide"
               using t arr_coincidence H.ide_dom H.ide_cod by simp
             moreover have "t \<in> H.hom (H.dom t) (H.cod t)"
               using t arr_coincidence by auto
             ultimately
             show "((H.dom t, H.cod t), t) \<in>
                      (Collect H.ide \<times> Collect H.ide) \<times>
                         (\<Union>x\<in>Collect H.ide \<times> Collect H.ide. H.hom (fst x) (snd x))"
               by auto
           qed
           moreover have "inj_on (\<lambda>t. ((H.dom t, H.cod t), t)) (Collect arr)"
             by (intro inj_onI) blast
           ultimately show ?thesis
             using small_image_iff
                   smaller_than_small
                     [of _ "(\<lambda>t. ((H.dom t, H.cod t), t)) ` Collect arr"]
             by blast
         qed
         hence "small_rts R"
           using small_rts_def rts_axioms small_rts_axioms.intro by auto
         thus "small_rts R'.resid"
           using R'.preserves_reflects_small_rts by blast
       qed
       have "inverse_simulations R'.resid R R'.map\<^sub>e\<^sub>x\<^sub>t R'.map'\<^sub>e\<^sub>x\<^sub>t"
         using R'.inverse_simulations_axioms by auto
       thus ?thesis
         using R'.rts_axioms R'.extensional_rts_axioms R'.small_rts_axioms
               inverse_simulations_sym
         by meson
     qed

     text\<open>
       We now choose some RTS with the properties asserted by the previous lemma,
       along with the invertible simulations that relate it to @{term R}.
     \<close>

     definition R' :: "'A resid"
     where "R' \<equiv> SOME R'. \<exists>UP DN. small_rts R' \<and> extensional_rts R' \<and>
                                    inverse_simulations resid R' UP DN"

     definition UP :: "'A \<Rightarrow> ('O, 'A) arr"
     where "UP \<equiv> SOME UP. \<exists>DN. small_rts R' \<and> extensional_rts R' \<and>
                                 inverse_simulations resid R' UP DN"

     definition DN :: "('O, 'A) arr \<Rightarrow> 'A"
     where "DN \<equiv> SOME DN. small_rts R' \<and> extensional_rts R' \<and>
                            inverse_simulations resid R' UP DN"

     lemma R'_prop:
     shows "\<exists>UP DN. small_rts R' \<and> extensional_rts R' \<and>
                      inverse_simulations R R' UP DN"
       unfolding R'_def
       using small_Obj ex_isomorphic_image_rts
             someI_ex
               [of "\<lambda>R'. \<exists>UP DN. small_rts R' \<and> extensional_rts R' \<and>
                                   inverse_simulations R R' UP DN"]
       by auto

     sublocale R': extensional_rts R'
       using R'_prop by simp
     sublocale R': small_rts R'
       using R'_prop by simp

     lemma extensional_rts_R':
     shows "extensional_rts R'"
       ..

     lemma small_rts_R':
     shows "small_rts R'"
       ..

     sublocale UP_DN: inverse_simulations R R' UP DN
       using small_Obj R'_prop UP_def DN_def
             someI_ex [of "\<lambda>UP. \<exists>DN. inverse_simulations resid R' UP DN"]
             someI_ex [of "\<lambda>DN. inverse_simulations resid R' UP DN"]
       by auto

     lemma inverse_simulations_UP_DN:
     shows "inverse_simulations resid R' UP DN"
       ..

     lemma R'_src_char:
     shows "R'.src = DN \<circ> src \<circ> UP"
     proof -
       have "\<And>t. DN (UP (R'.src t)) = DN (src (UP t))"
         by (metis H.dom_null R'.con_arr_src(2) R'.ide_src R'.not_arr_null R'.src_def
             UP_DN.F.extensional UP_DN.F.preserves_con UP_DN.F.preserves_ide
             null_coincidence src_dom V.src_eqI)
       moreover have "\<And>t. DN (UP (R'.src t)) = R'.src t"
         using R'.arr_src_iff_arr R'.src_def UP_DN.inv
         by (metis (no_types, lifting) comp_apply)
       ultimately show ?thesis by auto
     qed

     lemma R'_trg_char:
     shows "R'.trg = DN \<circ> trg \<circ> UP"
     proof -
       have "\<And>t. DN (UP (R'.trg t)) = DN (trg (UP t))"
         by (metis R'.arr_trg_iff_arr UP_DN.F.extensional UP_DN.F.preserves_trg
             V.null_is_zero(2) V.trg_def)
       moreover have "\<And>t. DN (UP (R'.trg t)) = R'.trg t"
         using R'.arr_trg_iff_arr R'.trg_def UP_DN.inv
         by (metis (no_types, lifting) R'.src_def R'.src_trg comp_apply)
       ultimately show ?thesis by auto
     qed

     text\<open>
       We transport the horizontal composition @{term hcomp} to \<open>R'\<close> via
       the isomorphisms @{term UP} and @{term DN}.
     \<close>

     abbreviation hcomp' :: "'A resid"  (infixr \<open>\<star>\<acute>\<close> 53)
     where "t \<star>\<acute> u \<equiv> DN (UP t \<star> UP u)"

     interpretation H': Category.partial_magma hcomp'
       by unfold_locales
          (metis H_composable_char R'.not_arr_null UP_DN.F.extensional
           UP_DN.F.preserves_reflects_arr UP_DN.G.extensional)

     lemma H'_null_char:
     shows "H'.null = DN null"
       using arr_coincidence
       by (metis H'.null_is_zero(2) R'.not_arr_null UP_DN.F.extensional
           hcomp_Null(2) null_char)

     interpretation H': partial_composition \<open>\<lambda>t u. DN (hcomp (UP t) (UP u))\<close> ..

     lemma H'_ide_char:
     shows "H'.ide t \<longleftrightarrow> H.ide (UP t)"
     proof
       have 1: "\<And>f. \<lbrakk>arr f; Dom f = Cod (UP t); t \<star>\<acute> t \<noteq> DN null;
                     \<And>t u. (t \<star> u \<noteq> null) = (arr t \<and> arr u \<and> Dom t = Cod u);
                     \<forall>f. (f \<star>\<acute> t \<noteq> DN null \<longrightarrow> f \<star>\<acute> t = f) \<and>
                         (t \<star>\<acute> f \<noteq> DN null \<longrightarrow> t \<star>\<acute> f = f)\<rbrakk>
                       \<Longrightarrow> f \<star> UP t = f"
          by (metis (no_types, lifting) UP_DN.G.preserves_reflects_arr
              UP_DN.inv'_simp arr_hcomp)
       have 2: "\<And>f. \<lbrakk>arr f; Dom (UP t) = Cod f; t \<star>\<acute> t \<noteq> DN null;
                     \<And>t u. (t \<star> u \<noteq> null) = (arr t \<and> arr u \<and> Dom t = Cod u);
                     \<forall>f. (f \<star>\<acute> t \<noteq> DN null \<longrightarrow> f \<star>\<acute> t = f) \<and>
                         (t \<star>\<acute> f \<noteq> DN null \<longrightarrow> t \<star>\<acute> f = f)\<rbrakk>
                       \<Longrightarrow> UP t \<star> f = f"
          by (metis (no_types, lifting) UP_DN.G.preserves_reflects_arr
              UP_DN.inv'_simp arr_hcomp)
       show "H'.ide t \<Longrightarrow> obj (UP t)"
         unfolding H'.ide_def H.ide_def
         using H'_null_char H_composable_char
         apply auto[1]
            apply (metis UP_DN.F.preserves_reflects_arr)
           apply metis
         using 1 2 by blast+
       show "obj (UP t) \<Longrightarrow> H'.ide t"
         unfolding H'.ide_def H.ide_def
         apply (auto simp add: H'_null_char H_composable_char)[1]
          apply (metis H_composable_char UP_DN.F.extensional UP_DN.inv_simp)
         by (metis H_composable_char UP_DN.F.extensional UP_DN.inv_simp)
     qed

     lemma H'_domains_char:
     shows "H'.domains t = DN ` H.domains (UP t)"
     proof -
       have "{a. H.ide (UP a) \<and> t \<star>\<acute> a \<noteq> DN null} =
             DN ` {a. H.ide a \<and> UP t \<star> a \<noteq> null}"
       proof
         show "{a. H.ide (UP a) \<and> t \<star>\<acute> a \<noteq> DN null} \<subseteq>
               DN ` {a. H.ide a \<and> UP t \<star> a \<noteq> null}"
         proof
           fix a
           assume a: "a \<in> {a. H.ide (UP a) \<and> t \<star>\<acute> a \<noteq> DN null}"
           have 1: "H.ide (UP a) \<and> UP t \<star> UP a \<noteq> null"
             using a by auto
           moreover have "a = DN (UP a)"
             using a 1
             by (metis (no_types, opaque_lifting) H_composable_char
                 UP_DN.F.preserves_reflects_arr UP_DN.inv comp_apply)
           ultimately show "a \<in> DN ` {a. H.ide a \<and> UP t \<star> a \<noteq> null}" by blast
         qed
         show "DN ` {a. H.ide a \<and> UP t \<star> a \<noteq> null} \<subseteq>
               {a. H.ide (UP a) \<and> t \<star>\<acute> a \<noteq> DN null}"
         proof
           fix a
           assume a: "a \<in> DN ` {a. H.ide a \<and> UP t \<star> a \<noteq> null}"
           obtain UPa
           where UPa: "a = DN UPa \<and> UPa \<in> {a. H.ide a \<and> UP t \<star> a \<noteq> null}"
             using a by blast
           have "UPa = UP a"
             using UPa H_composable_char UP_DN.inv' comp_apply by auto
           thus "a \<in> {a. H.ide (UP a) \<and> DN (UP t \<star> UP a) \<noteq> DN null}"
             using UPa null_coincidence
             by (metis (mono_tags, lifting) H.ext UP_DN.G.preserves_reflects_arr
                 arr_coincidence mem_Collect_eq V.not_arr_null)
         qed
       qed
       thus ?thesis
         unfolding H'.domains_def H.domains_def
         using H'_ide_char H'_null_char null_coincidence by simp
     qed

     lemma H'_codomains_char:
     shows "H'.codomains t = DN ` H.codomains (UP t)"
     proof -
       have "{b. H.ide (UP b) \<and> b \<star>\<acute> t \<noteq> DN null} =
             DN ` {b. H.ide b \<and> b \<star> UP t \<noteq> null}"
       proof
         show "{b. H.ide (UP b) \<and> b \<star>\<acute> t \<noteq> DN null} \<subseteq>
               DN ` {b. H.ide b \<and> b \<star> UP t \<noteq> null}"
         proof
           fix b
           assume b: "b \<in> {b. H.ide (UP b) \<and> b \<star>\<acute> t \<noteq> DN null}"
           have "DN (UP b) \<in> DN ` {b. H.ide b \<and> b \<star> UP t \<noteq> null}"
             using b by auto
           moreover have "DN (UP b) = b"
             using b
             by (metis (no_types, lifting) H'.ide_def H'_ide_char
                 H.comp_ide_self mem_Collect_eq)
           ultimately show "b \<in> DN ` {b. H.ide b \<and> b \<star> UP t \<noteq> null}" by auto
         qed
         show "DN ` {b. H.ide b \<and> b \<star> UP t \<noteq> null} \<subseteq>
               {b. H.ide (UP b) \<and> b \<star>\<acute> t \<noteq> DN null}"
         proof
           fix b
           assume b: "b \<in> DN ` {b. H.ide b \<and> b \<star> UP t \<noteq> null}"
           obtain UPb
           where UPb: "b = DN UPb \<and> UPb \<in> {b. H.ide b \<and> b \<star> UP t \<noteq> null}"
             using b by blast
           have "UPb = UP b"
             using UPb H_composable_char UP_DN.inv' comp_apply by auto
           thus "b \<in> {b. H.ide (UP b) \<and> DN (UP b \<star> UP t) \<noteq> DN null}"
             using UPb null_coincidence arr_coincidence
             by (metis (mono_tags, lifting) H.ext UP_DN.G.preserves_reflects_arr
                 mem_Collect_eq V.not_arr_null)
         qed
       qed
       thus ?thesis
         unfolding H'.codomains_def H.codomains_def
         using H'_ide_char H'_null_char null_coincidence by simp
     qed

     lemma H'_arr_char:
     shows "H'.arr t = H.arr (UP t)"
       unfolding H'.arr_def H.arr_def
       using H'_domains_char H'_codomains_char by auto

     lemma H'_seq_char:
     shows "H'.seq t u \<longleftrightarrow> H.seq (UP t) (UP u)"
       by (simp add: H'_arr_char)

     sublocale H': category hcomp'
     proof
       show "\<And>g f. g \<star>\<acute> f \<noteq> H'.null \<Longrightarrow> H'.seq g f"
         using H'_null_char H'_seq_char UP_DN.G.extensional by auto
       show "\<And>f. (H'.domains f \<noteq> {}) = (H'.codomains f \<noteq> {})"
         using H'_domains_char H'_codomains_char H.has_domain_iff_has_codomain
         by simp
       show "\<And>h g f. \<lbrakk>H'.seq h g; H'.seq (DN (UP h \<star> UP g)) f\<rbrakk> \<Longrightarrow> H'.seq g f"
         by (metis H'_seq_char H.match_1 UP_DN.inv'_simp arr_coincidence)
       show "\<And>h g f. \<lbrakk>H'.seq h (g \<star>\<acute> f); H'.seq g f\<rbrakk> \<Longrightarrow> H'.seq h g"
         using H'_seq_char H_seq_char by auto
       show "\<And>g f h. \<lbrakk>H'.seq g f; H'.seq h g\<rbrakk> \<Longrightarrow> H'.seq (h \<star>\<acute> g) f"
         using H'_arr_char H_seq_char by auto
       show "\<And>g f h. \<lbrakk>H'.seq g f; H'.seq h g\<rbrakk> \<Longrightarrow> (h \<star>\<acute> g) \<star>\<acute> f = h \<star>\<acute> g \<star>\<acute> f"
         using H'_seq_char H.comp_assoc UP_DN.inv' by auto
     qed

     lemma hcomp'_is_category:
     shows "category hcomp'"
       ..

     lemma H'_dom_char:
     shows "H'.dom = DN \<circ> H.dom \<circ> UP"
     proof
       fix t
       show "H'.dom t = (DN \<circ> H.dom \<circ> UP) t"
       proof (cases "arr (UP t)")
         show "\<not> arr (UP t) \<Longrightarrow> ?thesis"
           by (metis H'.dom_def H'.domains_char H'_arr_char H'_null_char
               H.dom_null H_arr_char UP_DN.F.extensional
               UP_DN.F.preserves_reflects_arr arr_char comp_def
               null_coincidence)
         assume t: "arr (UP t)"
         have "(DN \<circ> H.dom \<circ> UP) t = DN (H.dom (UP t))"
           using t by auto
         also have "... = H'.dom t"
           using t H'_domains_char H'_arr_char arr_coincidence H.dom_in_domains
                 H.has_domain_iff_arr
           by (intro H'.dom_eqI') auto
         finally show ?thesis by auto
       qed
     qed

     lemma H'_cod_char:
     shows "H'.cod = DN \<circ> H.cod \<circ> UP"
     proof
       fix t
       show "H'.cod t = (DN \<circ> H.cod \<circ> UP) t"
       proof (cases "arr (UP t)")
         show "\<not> arr (UP t) \<Longrightarrow> ?thesis"
           by (metis H'.cod_def H'.codomains_char H'_arr_char H'_null_char
               H.cod_null H_arr_char UP_DN.F.extensional
               UP_DN.F.preserves_reflects_arr arr_char comp_def
               null_coincidence)
         assume t: "arr (UP t)"
         have "(DN \<circ> H.cod \<circ> UP) t = DN (H.cod (UP t))"
           using t by auto
         also have "... = H'.cod t"
           using t H'_codomains_char H'_arr_char arr_coincidence
                 H.cod_in_codomains H.has_codomain_iff_arr
           by (intro H'.cod_eqI') auto
         finally show ?thesis by auto
       qed
     qed

     lemma null'_coincidence [simp]:
     shows "H'.null = R'.null"
       by (simp add: H'_null_char UP_DN.G.extensional)

     lemma arr'_coincidence [simp]:
     shows "H'.arr = R'.arr"
       using H'_arr_char UP_DN.F.preserves_reflects_arr arr_coincidence by auto

     lemma H'_hom_char:
     shows "H'.hom a b = DN ` H.hom (UP a) (UP b)"
     proof
       show "H'.hom a b \<subseteq> DN ` H.hom (UP a) (UP b)"
       proof
         fix t
         assume t: "t \<in> H'.hom a b"
         have "UP t \<in> H.hom (UP a) (UP b)"
         proof
           have a: "V.ide (UP a)"
             using t arr'_coincidence H'_ide_char UP_DN.F.preserves_ide
             by (metis H'.arr_dom H'.dom_dom H'.ide_char' H'.in_homE
                 H_ide_is_V_ide mem_Collect_eq)
           have b: "V.ide (UP b)"
             using t arr'_coincidence H'_ide_char UP_DN.F.preserves_ide
             by (metis H'.arr_cod H'.cod_cod H'.ide_char' H'.in_homE
                 H_ide_is_V_ide mem_Collect_eq)
           show "H.in_hom (UP t) (UP a) (UP b)"
           proof
             show 1: "H.arr (UP t)"
               using t arr_coincidence arr'_coincidence
                     UP_DN.F.preserves_reflects_arr
               by auto
             show "H.dom (UP t) = UP a"
             proof -
               have 2: "DN (H.dom (UP t)) = a"
                 using t a 1 H'_dom_char by auto
               also have "... = DN (UP a)"
                 using t a UP_DN.inv
                 by (metis (no_types, lifting) UP_DN.F.preserves_reflects_arr
                     comp_apply V.ide_implies_arr)
               finally have "DN (H.dom (UP t)) = DN (UP a)" by blast
               thus ?thesis
                 by (metis 1 2 H.arr_dom_iff_arr UP_DN.inv'
                     arr_coincidence comp_apply)
             qed
             show "H.cod (UP t) = UP b"
             proof -
               have 2: "DN (H.cod (UP t)) = b"
                 using t b 1 arr_coincidence H'_cod_char by auto
               also have "... = DN (UP b)"
                 using t b UP_DN.inv
                 by (metis (no_types, lifting) UP_DN.F.preserves_reflects_arr
                     comp_apply V.ide_implies_arr)
               finally have "DN (H.cod (UP t)) = DN (UP b)" by blast
               thus ?thesis
                 by (metis 1 2 H.arr_cod_iff_arr UP_DN.inv'
                     arr_coincidence comp_apply)
             qed
           qed
         qed
         moreover have "DN (UP t) = t"
           using t UP_DN.inv
           by (metis (no_types, lifting) H'.in_homE arr'_coincidence
               comp_apply mem_Collect_eq)
         ultimately show "t \<in> DN ` H.hom (UP a) (UP b)"
           by (simp add: rev_image_eqI)
       qed
       show "DN ` H.hom (UP a) (UP b) \<subseteq> H'.hom a b"
       proof
         fix t'
         assume t': "t' \<in> DN ` H.hom (UP a) (UP b)"
         obtain t where t: "t \<in> H.hom (UP a) (UP b) \<and> t' = DN t"
           using t' by blast
         have "DN t \<in> H'.hom a b"
         proof
           show "H'.in_hom (DN t) a b"
           proof
             show "H'.arr (DN t)"
               using t H'_arr_char arr_coincidence by fastforce
             show "H'.dom (DN t) = a"
               using t H'_dom_char
               by (metis (no_types, lifting) Fun.comp_def H'.ide_char'
                   H'_ide_char H.ide_dom H.in_homE H_arr_char UP_DN.inv
                   UP_DN.inv' arr'_coincidence arr_char mem_Collect_eq)
             show "H'.cod (DN t) = b"
               using t H'_cod_char
               by (metis (no_types, lifting) Fun.comp_def H'.ide_char'
                   H'_ide_char H.ide_cod H.in_homE H_arr_char
                   UP_DN.inv UP_DN.inv' arr'_coincidence arr_char
                   mem_Collect_eq)
           qed
         qed
         thus "t' \<in> H'.hom a b"
           using t by blast
       qed
     qed

     interpretation dom': simulation R' R' H'.dom
       using H'_dom_char simulation_comp simulation_dom
             UP_DN.F.simulation_axioms UP_DN.G.simulation_axioms
       by auto

     interpretation cod': simulation R' R' H'.cod
       using H'_cod_char simulation_comp simulation_cod
             UP_DN.F.simulation_axioms UP_DN.G.simulation_axioms
       by auto

     lemma R'_con_char:
     shows "R'.con t u \<longleftrightarrow> V.con (UP t) (UP u)"
       by (metis UP_DN.F.preserves_con UP_DN.F.preserves_reflects_arr
           UP_DN.G.preserves_con UP_DN.inv comp_apply
           residuation.con_implies_arr(1-2) V.residuation_axioms)

     sublocale R'R': fibered_product_rts R' R' R' H'.dom H'.cod ..

     sublocale H': simulation R'R'.resid R'
                     \<open>\<lambda>t. if R'R'.arr t then fst t \<star>\<acute> snd t else R'.null\<close>
     proof
       show "\<And>t. \<not> R'R'.arr t \<Longrightarrow>
                      (if R'R'.arr t then fst t \<star>\<acute> snd t else R'.null) = R'.null"
         by auto
       fix t u
       assume tu: "R'R'.con t u"
       show 1: "R'.con (if R'R'.arr t then fst t \<star>\<acute> snd t else R'.null)
                       (if R'R'.arr u then fst u \<star>\<acute> snd u else R'.null)"
       proof -
         have "UP (fst t \<star>\<acute> snd t) = UP (fst t) \<star> UP (snd t) \<and>
               UP (fst u \<star>\<acute> snd u) = UP (fst u) \<star> UP (snd u)"
           using tu arr_coincidence null_coincidence UP_DN.inv' H.ext
           apply auto[1]
           by (metis (no_types, lifting) UP_DN.F.extensional
               UP_DN.G.preserves_reflects_arr UP_DN.inv'_simp)+
         moreover have "UP (fst t) \<star> UP (snd t) \<frown> UP (fst u) \<star> UP (snd u)"
         proof -
           have "RR.con (UP (fst t), UP (snd t)) (UP (fst u), UP (snd u))"
             by (metis H'.seqI H'_seq_char H.seqE R'R'.arr_char R'R'.con_char
                 R'R'.residuation_axioms R'_con_char RR.con_char arr'_coincidence
                 fst_conv residuation.con_implies_arr(1-2) snd_conv tu)
           thus ?thesis
             using H.preserves_con RR.con_implies_arr(1-2) by force
         qed
         ultimately show ?thesis
           using tu
           by (simp add: R'R'.con_implies_arr(1) R'R'.con_implies_arr(2))
       qed
       show "(if R'R'.arr (R'R'.resid t u)
              then fst (R'R'.resid t u) \<star>\<acute> snd (R'R'.resid t u)
              else R'.null) =
             R' (if R'R'.arr t then fst t \<star>\<acute> snd t else R'.null)
                (if R'R'.arr u then fst u \<star>\<acute> snd u else R'.null)"
       proof -
         have "fst (R'R'.resid t u) \<star>\<acute> snd (R'R'.resid t u) =
               R' (fst t \<star>\<acute> snd t) (fst u \<star>\<acute> snd u)"
         proof -
           have "UP (fst (R'R'.resid t u) \<star>\<acute> snd (R'R'.resid t u)) =
                 UP (R' (fst t \<star>\<acute> snd t) (fst u \<star>\<acute> snd u))"
           proof -
             have "UP (fst (R'R'.resid t u) \<star>\<acute> snd (R'R'.resid t u)) =
                   UP (R' (fst t) (fst u) \<star>\<acute> R' (snd t) (snd u))"
               using tu R'R'.con_char R'R'.resid_def by auto
             also have "... = UP (R' (fst t) (fst u)) \<star> UP (R' (snd t) (snd u))"
               using tu
               by (metis H.ext UP_DN.inv' arr_coincidence comp_apply
                   null_coincidence)
             also have "... = resid (UP (fst t)) (UP (fst u)) \<star>
                                resid (UP (snd t)) (UP (snd u))"
               using R'R'.con_char UP_DN.F.preserves_resid tu by presburger
             also have "... = (UP (fst t) \<star> UP (snd t)) \\ (UP (fst u) \<star> UP (snd u))"
               using tu 1 H.preserves_resid H.seqE R'.con_implies_arr(1-2)
                     R'.not_arr_null R'R'.con_char R'_con_char RR.arr_char
                     RR.arr_resid_iff_con RR.con_char RR.resid_def
                     UP_DN.G.extensional
               by (metis (no_types, lifting) H'.seqI H'_arr_char H'_seq_char
                   hpar_arr_resid resid_hcomp(2))
             also have "... = UP (fst t \<star>\<acute> snd t) \\ UP (fst u \<star>\<acute> snd u)"
             proof -
               have "UP (fst t \<star>\<acute> snd t) = UP (fst t) \<star> UP (snd t) \<and>
                     UP (fst u \<star>\<acute> snd u) = UP (fst u) \<star> UP (snd u)"
                 using H'.seqI R'R'.arr_char R'R'.con_implies_arr(1-2) tu by auto
               thus ?thesis
                 using tu H.ext UP_DN.inv' arr_coincidence comp_apply
                       null_coincidence
                 by auto
             qed
             also have "... = UP (R' (fst t \<star>\<acute> snd t) (fst u \<star>\<acute> snd u))"
               using "1" R'R'.con_implies_arr(1) R'R'.con_implies_arr(2) tu by auto
             finally show ?thesis by blast
           qed
           thus ?thesis
             by (metis (no_types, lifting) H'.seqI R'R'.arr_char R'R'.arr_resid
                 UP_DN.F.preserves_reflects_arr UP_DN.inv_simp arr'_coincidence tu)
         qed
         thus ?thesis
           using tu 1 H.preserves_resid by auto
       qed
     qed

     proposition is_locally_small_rts_category:
     shows "locally_small_rts_category R' hcomp'"
     proof
       show "H'.null = R'.null"
         by (simp add: H'_null_char UP_DN.G.extensional)
       show "H'.arr = R'.arr"
         using H'_arr_char UP_DN.F.preserves_reflects_arr arr_coincidence by auto
       show "\<And>t. R'.src (H'.dom t) = H'.dom t"
         using R'_src_char H'_dom_char R'.arr_src_iff_arr UP_DN.G.extensional
               UP_DN.G.preserves_reflects_arr
         apply auto[1]
         by (metis (no_types, lifting) R'.not_arr_null UP_DN.inv'_simp src_dom)
       show "\<And>a b. small (H'.hom a b)"
         using H'_hom_char small_homs by simp
     qed

  end

subsection "Functoriality"

  locale rts_functor_of_enriched_functor =
    universe arr_type +
    RTS: rtscat arr_type +
    A: rts_enriched_category arr_type Obj\<^sub>A Hom\<^sub>A Id\<^sub>A Comp\<^sub>A +
    B: rts_enriched_category arr_type Obj\<^sub>B Hom\<^sub>B Id\<^sub>B Comp\<^sub>B +
    EF: rts_enriched_functor
          Obj\<^sub>A Hom\<^sub>A Id\<^sub>A Comp\<^sub>A Obj\<^sub>B Hom\<^sub>B Id\<^sub>B Comp\<^sub>B F\<^sub>o F\<^sub>a
  for Obj\<^sub>A :: "'a set"
  and Hom\<^sub>A :: "'a \<Rightarrow> 'a \<Rightarrow> 'A rtscatx.arr"
  and Id\<^sub>A :: "'a \<Rightarrow> 'A rtscatx.arr"
  and Comp\<^sub>A :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'A rtscatx.arr"
  and Obj\<^sub>B :: "'b set"
  and Hom\<^sub>B :: "'b \<Rightarrow> 'b \<Rightarrow> 'A rtscatx.arr"
  and Id\<^sub>B :: "'b \<Rightarrow> 'A rtscatx.arr"
  and Comp\<^sub>B :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'A rtscatx.arr"
  and F\<^sub>o :: "'a \<Rightarrow> 'b"
  and F\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> 'A rtscatx.arr"
  begin

    interpretation A: rts_category_of_enriched_category
                        arr_type Obj\<^sub>A Hom\<^sub>A Id\<^sub>A Comp\<^sub>A
      ..
    interpretation B: rts_category_of_enriched_category
                        arr_type Obj\<^sub>B Hom\<^sub>B Id\<^sub>B Comp\<^sub>B
      ..

    definition F
    where "F t \<equiv> if residuation.arr A.resid t
                  then B.MkArr (F\<^sub>o (A.Dom t)) (F\<^sub>o (A.Cod t))
                               (RTS.Map (F\<^sub>a (A.Dom t) (A.Cod t)) (A.Trn t))
                  else ResiduatedTransitionSystem.partial_magma.null B.resid"

    lemma preserves_arr:
    assumes "A.H.arr f"
    shows "B.H.arr (F f)"
    proof -
      let ?a = "A.Dom f"
      let ?b = "A.Cod f"
      show 1: "B.H.arr (F f)"
      proof -
        have "B.arr (F f)"
          unfolding F_def
          using assms A.arr_char B.arr_MkArr A.arr_coincidence
            B.arr_coincidence
          apply (simp, intro B.arr_MkArr)
            apply blast
           apply blast
          using EF.is_local_simulation simulation.preserves_reflects_arr
          by metis
        thus ?thesis by auto
      qed
    qed

    sublocale rts_functor A.resid A.hcomp B.resid B.hcomp F
    proof
      show "\<And>f. \<not> A.H.arr f \<Longrightarrow> F f = B.H.null"
        using F_def A.arr_coincidence B.null_coincidence by simp
      show 1: "\<And>f. A.H.arr f \<Longrightarrow> B.H.arr (F f)"
        using preserves_arr by simp
      fix f
      assume f: "A.H.arr f"
      have 0: "A.arr (A.MkArr (A.Dom f) (A.Dom f)
                         (RTS.Map (Id\<^sub>A (A.Dom f)) RTS.One.the_arr))"
        using f A.arr_char A.arr_coincidence A.Id_in_hom RTS.Map_ide
        by (metis (no_types, lifting) A.H_dom_char A.dom.preserves_reflects_arr)
      have 1: "B.arr (B.MkArr (F\<^sub>o (A.Dom f)) (F\<^sub>o (A.Cod f))
                        (RTS.Map (F\<^sub>a (A.Dom f) (A.Cod f)) (A.Trn f)))"
        using f 1 F_def B.H_dom_char B.arr_char B.null_char B.arr_coincidence
              B.null_coincidence
        by (intro B.arr_MkArr) auto
      have 2: "A.arr (A.MkArr (A.Cod f) (A.Cod f)
                        (RTS.Map (Id\<^sub>A (A.Cod f)) RTS.One.the_arr))"
        using f A.arr_char A.arr_coincidence A.H.ideD(1)
              A.Id_yields_horiz_ide
        by force
      show "B.H.dom (F f) = F (A.H.dom f)"
      proof (intro B.arr_eqI)
        show "B.H.dom (F f) \<noteq> B.null"
          using f 1 F_def B.H_dom_char B.null_char by auto
        show "F (A.H.dom f) \<noteq> B.null"
          using f 0 F_def A.H_dom_char B.null_char by auto
        show "B.Dom (B.H.dom (F f)) = B.Dom (F (A.H.dom f))"
          using f 0 1 F_def A.H_dom_char B.H_dom_char by simp
        show "B.Cod (B.H.dom (F f)) = B.Cod (F (A.H.dom f))"
          using f 0 1 F_def A.H_dom_char B.H_dom_char by simp
        show "B.Trn (B.H.dom (F f)) = B.Trn (F (A.H.dom f))"
        proof -
          have "B.Trn (F (A.H.dom f)) =
                RTS.Map (F\<^sub>a (A.Dom f) (A.Dom f))
                  (RTS.Map (Id\<^sub>A (A.Dom f)) RTS.One.the_arr)"
            using f 0 F_def A.H_dom_char B.H_dom_char EF.preserves_Id
                  RTS.Map_comp
            by auto
          also have "... = RTS.Map (F\<^sub>a (A.Dom f) (A.Dom f) \<cdot> Id\<^sub>A (A.Dom f))
                             RTS.One.the_arr"
            using f RTS.Map_comp A.Id_in_hom
                  EF.preserves_Hom [of "A.Dom f" "A.Dom f"]
                  EF.preserves_Obj [of "A.Dom f"] comp_apply
            apply auto[1]
            using A.arr_char [of f] by fastforce
          also have "... = RTS.Map (Id\<^sub>B (F\<^sub>o (A.Dom f))) RTS.One.the_arr"
            using f 0 1 EF.preserves_Id A.arr_char by simp
          also have "... = B.Trn (B.H.dom (F f))"
            using f 0 1 F_def by (simp add: B.H_dom_simp B.H_cod_simp)
          finally show ?thesis by simp
        qed
      qed
      show "B.H.cod (F f) = F (A.H.cod f)"
      proof (intro B.arr_eqI)
        show "B.H.cod (F f) \<noteq> B.null"
          using f 1 F_def B.H_cod_char B.null_char by auto
        show "F (A.H.cod f) \<noteq> B.null"
          using f 2 F_def A.H_cod_char B.null_char by auto
        show "B.Dom (B.H.cod (F f)) = B.Dom (F (A.H.cod f))"
          using f 2 F_def A.H_cod_char B.H_cod_char B.null_char
                B.cod.extensional \<open>B.H.cod (F f) \<noteq> B.null\<close>
          by fastforce
        show "B.Cod (B.H.cod (F f)) = B.Cod (F (A.H.cod f))"
          using f 2 F_def A.H_cod_char B.H_cod_char B.null_char
                B.cod.extensional \<open>B.H.cod (F f) \<noteq> B.null\<close>
          by fastforce
        show "B.Trn (B.H.cod (F f)) = B.Trn (F (A.H.cod f))"
        proof -
          have "B.Trn (F (A.H.cod f)) =
                RTS.Map (F\<^sub>a (A.Cod f) (A.Cod f))
                  (RTS.Map (Id\<^sub>A (A.Cod f)) RTS.One.the_arr)"
            using f 2 F_def A.H_cod_char B.H_cod_char EF.preserves_Id
                  RTS.Map_comp
            by auto
          also have "... =
                     RTS.Map (F\<^sub>a (A.Cod f) (A.Cod f) \<cdot> Id\<^sub>A (A.Cod f))
                       RTS.One.the_arr"
            using f 0 1 2 A.Id_in_hom
                  EF.preserves_Hom [of "A.Cod f" "A.Cod f"]
                  EF.preserves_Obj [of "A.Cod f"] comp_apply RTS.Map_comp
            apply auto[1]
            using A.arr_char [of f] by fastforce
          also have "... = RTS.Map (Id\<^sub>B (F\<^sub>o (A.Cod f))) RTS.One.the_arr"
            using f 0 1 EF.preserves_Id A.arr_char by simp
          also have "... = B.Trn (B.H.cod (F f))"
            using f 0 1 F_def by (auto simp add: B.H_dom_simp B.H_cod_simp)
          finally show ?thesis by simp
        qed
      qed
      next
      fix f g
      assume fg: "A.H.seq g f"
      show "F (A.hcomp g f) = B.hcomp (F g) (F f)"
      proof (intro B.arr_eqI)
        show "F (A.hcomp g f) \<noteq> B.null"
          using fg F_def B.null_char by auto
        have 2: "B.Dom (F g) = B.Cod (F f)"
          using fg preserves_arr F_def A.H_seq_char by auto
        show 3: "B.hcomp (F g) (F f) \<noteq> B.null"
          using fg 2 preserves_arr B.null_char B.arr_hcomp [of "F g" "F f"]
                A.arr_coincidence B.arr_coincidence A.H_seq_char
                B.V.not_arr_null
          by auto
        show "B.Dom (F (A.hcomp g f)) = B.Dom (B.hcomp (F g) (F f))"
          using fg F_def "3" A.H_seq_char B.H_composable_char by auto
        show "B.Cod (F (A.hcomp g f)) = B.Cod (B.hcomp (F g) (F f))"
          using fg F_def "3" A.H_seq_char B.H_composable_char by auto
        show "B.Trn (F (A.hcomp g f)) = B.Trn (B.hcomp (F g) (F f))"
        proof -
          have "B.Trn (F (A.hcomp g f)) =
                RTS.Map (F\<^sub>a (A.Dom f) (A.Cod g))
                        (RTS.Map (Comp\<^sub>A (A.Dom f) (A.Cod f) (A.Cod g))
                                 (RTS.Pack (Hom\<^sub>A (A.Cod f) (A.Cod g))
                                           (Hom\<^sub>A (A.Dom f) (A.Cod f))
                                           (A.Trn g, A.Trn f)))"
            using fg F_def A.H_seq_char by auto
          also have "... = (RTS.Map (F\<^sub>a (A.Dom f) (A.Cod g)) \<circ>
                              RTS.Map (Comp\<^sub>A (A.Dom f) (A.Cod f) (A.Cod g)))
                             (RTS.Pack
                                (Hom\<^sub>A (A.Cod f) (A.Cod g))
                                (Hom\<^sub>A (A.Dom f) (A.Cod f))
                                (A.Trn g, A.Trn f))"
            using fg A.H_seq_char A.Comp_in_hom EF.preserves_Hom
                  RTS.Map_comp
            by auto    
          also have "... = RTS.Map (F\<^sub>a (A.Dom f) (A.Cod g) \<cdot>
                                      Comp\<^sub>A (A.Dom f) (A.Cod f) (A.Cod g))
                             (RTS.Pack (Hom\<^sub>A (A.Cod f) (A.Cod g))
                                       (Hom\<^sub>A (A.Dom f) (A.Cod f))
                                       (A.Trn g, A.Trn f))"
            using fg A.H_seq_char comp_apply A.Comp_in_hom EF.preserves_Hom
                  RTS.Map_comp
            apply auto[1]
            by (metis (no_types, lifting) A.arr_char RTS.seqI' comp_apply)
          also have "... = RTS.Map
                             (Comp\<^sub>B (F\<^sub>o (A.Dom f)) (F\<^sub>o (A.Cod f)) (F\<^sub>o (A.Cod g)) \<cdot>
                                (F\<^sub>a (A.Cod f) (A.Cod g) \<otimes> F\<^sub>a (A.Dom f) (A.Cod f)))
                             (RTS.Pack
                                (Hom\<^sub>A (A.Cod f) (A.Cod g))
                                (Hom\<^sub>A (A.Dom f) (A.Cod f))
                                (A.Trn g, A.Trn f))"
            using fg A.H_seq_char A.arr_char EF.preserves_Comp by auto
          also have "... = (RTS.Map
                             (Comp\<^sub>B (F\<^sub>o (A.Dom f)) (F\<^sub>o (A.Cod f)) (F\<^sub>o (A.Cod g))) \<circ>
                                RTS.Map
                                  (F\<^sub>a (A.Cod f) (A.Cod g) \<otimes> F\<^sub>a (A.Dom f) (A.Cod f)))
                             (RTS.Pack
                                (Hom\<^sub>A (A.Cod f) (A.Cod g))
                                (Hom\<^sub>A (A.Dom f) (A.Cod f))
                                (A.Trn g, A.Trn f))"
          proof -
            have "RTS.seq
                    (Comp\<^sub>B (F\<^sub>o (A.Dom f)) (F\<^sub>o (A.Cod f)) (F\<^sub>o (A.Cod g)))
                    (F\<^sub>a (A.Cod f) (A.Cod g) \<otimes> F\<^sub>a (A.Dom f) (A.Cod f))"
              using fg B.Comp_in_hom EF.preserves_Obj
              by (metis A.Comp_in_hom A.H.seqE A.H_arr_char EF.preserves_Comp
                  EF.preserves_Hom RTS.arrI RTS.seqI' RTS.tensor_agreement)
            thus ?thesis
              using RTS.Map_comp
                      [of "Comp\<^sub>B (F\<^sub>o (A.Dom f)) (F\<^sub>o (A.Cod f)) (F\<^sub>o (A.Cod g))"
                          "F\<^sub>a (A.Cod f) (A.Cod g) \<otimes> F\<^sub>a (A.Dom f) (A.Cod f)"]
              by argo
          qed
          also have "... = RTS.Map
                             (Comp\<^sub>B (F\<^sub>o (A.Dom f)) (F\<^sub>o (A.Cod f)) (F\<^sub>o (A.Cod g)))
                             (RTS.Map
                                (F\<^sub>a (A.Cod f) (A.Cod g) \<otimes> F\<^sub>a (A.Dom f) (A.Cod f))
                                (RTS.Pack
                                   (Hom\<^sub>A (A.Cod f) (A.Cod g))
                                   (Hom\<^sub>A (A.Dom f) (A.Cod f))
                                   (A.Trn g, A.Trn f)))"
            by simp
          also have "... = RTS.Map
                             (Comp\<^sub>B (F\<^sub>o (A.Dom f)) (F\<^sub>o (A.Cod f)) (F\<^sub>o (A.Cod g)))
                             ((RTS.Pack
                                 (RTS.cod (F\<^sub>a (A.Cod f) (A.Cod g)))
                                 (RTS.cod (F\<^sub>a (A.Dom f) (A.Cod f))) \<circ>
                                 product_simulation.map
                                   (A.HOM\<^sub>E\<^sub>C (A.Cod f) (A.Cod g))
                                   (A.HOM\<^sub>E\<^sub>C (A.Dom f) (A.Cod f))
                                   (RTS.Map (F\<^sub>a (A.Cod f) (A.Cod g)))
                                   (RTS.Map (F\<^sub>a (A.Dom f) (A.Cod f))) \<circ>
                                   RTS.Unpack
                                     (RTS.dom (F\<^sub>a (A.Cod f) (A.Cod g)))
                                     (RTS.dom (F\<^sub>a (A.Dom f) (A.Cod f))))
                                (RTS.Pack
                                   (Hom\<^sub>A (A.Cod f) (A.Cod g))
                                   (Hom\<^sub>A (A.Dom f) (A.Cod f))
                                   (A.Trn g, A.Trn f)))"
             using fg A.H_seq_char EF.preserves_Hom RTS.Map_prod
             by (metis (no_types, lifting) A.arr_char RTS.in_homE)
          also have "... = RTS.Map
                             (Comp\<^sub>B (F\<^sub>o (A.Dom f)) (F\<^sub>o (A.Cod f)) (F\<^sub>o (A.Cod g)))
                             (RTS.Pack
                                (Hom\<^sub>B (F\<^sub>o (A.Cod f)) (F\<^sub>o (A.Cod g)))
                                (Hom\<^sub>B (F\<^sub>o (A.Dom f)) (F\<^sub>o (A.Cod f)))
                                (product_simulation.map
                                   (A.HOM\<^sub>E\<^sub>C (A.Cod f) (A.Cod g))
                                   (A.HOM\<^sub>E\<^sub>C (A.Dom f) (A.Cod f))
                                   (RTS.Map (F\<^sub>a (A.Cod f) (A.Cod g)))
                                   (RTS.Map (F\<^sub>a (A.Dom f) (A.Cod f)))
                                   (RTS.Unpack
                                      (Hom\<^sub>A (A.Cod f) (A.Cod g))
                                      (Hom\<^sub>A (A.Dom f) (A.Cod f))
                                      (RTS.Pack
                                         (Hom\<^sub>A (A.Cod f) (A.Cod g))
                                         (Hom\<^sub>A (A.Dom f) (A.Cod f))
                                         (A.Trn g, A.Trn f)))))"
          proof -
            have "RTS.dom (F\<^sub>a (A.Dom f) (A.Cod f)) =
                  Hom\<^sub>A (A.Dom f) (A.Cod f)"
              using fg A.H_seq_char A.arr_char
                    EF.preserves_Hom [of "A.Dom f" "A.Cod f"]
              by auto
            moreover have "RTS.cod (F\<^sub>a (A.Dom f) (A.Cod f)) =
                           Hom\<^sub>B (F\<^sub>o (A.Dom f)) (F\<^sub>o (A.Cod f))"
              using fg A.H_seq_char A.arr_char
                    EF.preserves_Hom [of "A.Dom f" "A.Cod f"]
              by auto
            ultimately show ?thesis
              using fg A.H_seq_char A.arr_char
                    EF.preserves_Hom [of "A.Cod f" "A.Cod g"]
                    EF.preserves_Hom [of "A.Dom f" "A.Cod f"]
              by auto
          qed
          also have "... = RTS.Map
                             (Comp\<^sub>B (F\<^sub>o (A.Dom f)) (F\<^sub>o (A.Cod f)) (F\<^sub>o (A.Cod g)))
                             (RTS.Pack
                                (Hom\<^sub>B (F\<^sub>o (A.Cod f)) (F\<^sub>o (A.Cod g)))
                                (Hom\<^sub>B (F\<^sub>o (A.Dom f)) (F\<^sub>o (A.Cod f)))
                                (product_simulation.map
                                   (A.HOM\<^sub>E\<^sub>C (A.Cod f) (A.Cod g))
                                   (A.HOM\<^sub>E\<^sub>C (A.Dom f) (A.Cod f))
                                   (RTS.Map (F\<^sub>a (A.Cod f) (A.Cod g)))
                                   (RTS.Map (F\<^sub>a (A.Dom f) (A.Cod f)))
                                   (A.Trn g, A.Trn f)))"
          proof -
            interpret HOM: extensional_rts \<open>A.HOM\<^sub>E\<^sub>C (A.Cod f) (A.Cod g)\<close>
              using fg A.H_seq_char A.arr_char A.ide_Hom
              by (metis (no_types, lifting) EF.preserves_Hom RTS.arrD(1)
                  RTS.in_homE)
            interpret HOM': extensional_rts \<open>A.HOM\<^sub>E\<^sub>C (A.Dom f) (A.Cod f)\<close>
              using fg A.H_seq_char A.arr_char A.ide_Hom
              by (metis (no_types, lifting) EF.preserves_Hom RTS.arrD(1)
                  RTS.in_homE)
            interpret HOMxHOM': product_rts
                                  \<open>A.HOM\<^sub>E\<^sub>C (A.Cod f) (A.Cod g)\<close>
                                  \<open>A.HOM\<^sub>E\<^sub>C (A.Dom f) (A.Cod f)\<close>
              ..
            show ?thesis
              using A.H_arr_char A.H_seq_char fg by force
          qed
          also have "... = RTS.Map
                             (Comp\<^sub>B (F\<^sub>o (A.Dom f)) (F\<^sub>o (A.Cod f)) (F\<^sub>o (A.Cod g)))
                             (RTS.Pack
                                (Hom\<^sub>B (F\<^sub>o (A.Cod f)) (F\<^sub>o (A.Cod g)))
                                (Hom\<^sub>B (F\<^sub>o (A.Dom f)) (F\<^sub>o (A.Cod f)))
                                (RTS.Map (F\<^sub>a (A.Cod f) (A.Cod g)) (A.Trn g),
                                 RTS.Map (F\<^sub>a (A.Dom f) (A.Cod f)) (A.Trn f)))"
          proof -
            interpret F: simulation
                           \<open>A.HOM\<^sub>E\<^sub>C (A.Cod f) (A.Cod g)\<close>
                           \<open>B.HOM\<^sub>E\<^sub>C (F\<^sub>o (A.Cod f)) (F\<^sub>o (A.Cod g))\<close>
                           \<open>RTS.Map (F\<^sub>a (A.Cod f) (A.Cod g))\<close>
              using fg A.H_seq_char A.arr_char EF.preserves_Hom
              by (meson EF.is_local_simulation)
            interpret F': simulation
                            \<open>A.HOM\<^sub>E\<^sub>C (A.Dom f) (A.Cod f)\<close>
                            \<open>B.HOM\<^sub>E\<^sub>C (F\<^sub>o (A.Dom f)) (F\<^sub>o (A.Cod f))\<close>
                            \<open>RTS.Map (F\<^sub>a (A.Dom f) (A.Cod f))\<close>
              using fg A.H_seq_char A.arr_char EF.preserves_Hom
              by (meson EF.is_local_simulation)
            interpret FxF': product_simulation
                              \<open>A.HOM\<^sub>E\<^sub>C (A.Cod f) (A.Cod g)\<close>
                              \<open>A.HOM\<^sub>E\<^sub>C (A.Dom f) (A.Cod f)\<close>
                              \<open>B.HOM\<^sub>E\<^sub>C (F\<^sub>o (A.Cod f)) (F\<^sub>o (A.Cod g))\<close>
                              \<open>B.HOM\<^sub>E\<^sub>C (F\<^sub>o (A.Dom f)) (F\<^sub>o (A.Cod f))\<close>
                              \<open>RTS.Map (F\<^sub>a (A.Cod f) (A.Cod g))\<close>
                              \<open>RTS.Map (F\<^sub>a (A.Dom f) (A.Cod f))\<close>
              ..
            show ?thesis
              by (metis FxF'.map_simp fg A.H_seq_char A.arr_char)
          qed
          also have "... = B.Trn (B.hcomp (F g) (F f))"
            using fg 3 F_def A.H_seq_char B.Trn_hcomp B.H_composable_char
            by force
          finally show ?thesis by blast
        qed
      qed
      next
      show "\<And>t. \<not> A.arr t \<Longrightarrow> F t = B.null"
        unfolding F_def by simp
      show "\<And>t u. A.V.con t u \<Longrightarrow> B.V.con (F t) (F u)"
        unfolding F_def
        using A.V.con_implies_arr B.con_char EF.preserves_Obj
              EF.preserves_Hom A.arr_char A.con_char
        apply auto[1]
        apply (intro B.ConI conjI)
                  apply auto[11] (* 3 goals remain *)
        by (metis A.ConE EF.is_local_simulation
            simulation.preserves_reflects_arr simulation.preserves_con)+
      show "\<And>t u. A.V.con t u \<Longrightarrow> F (A.resid t u) = B.resid (F t) (F u)"
        unfolding F_def
        using A.V.con_implies_arr B.con_char EF.preserves_Obj EF.preserves_Hom
              A.arr_char B.null_char A.con_implies_Par
        apply auto[1]
           apply (metis (mono_tags, lifting) A.ConE A.resid_ne_Null_imp_Con
             EF.is_local_simulation simulation.preserves_resid)
          apply (metis (mono_tags, lifting) F_def
            \<open>\<And>u t. A.V.con t u \<Longrightarrow> B.V.con (F t) (F u)\<close>)
         apply (meson A.V.arr_resid)
        using A.V.arr_resid by force
    qed

    lemma is_rts_functor:
    shows "rts_functor A.resid A.hcomp B.resid B.hcomp F"
      ..

  end

section "RTS-Categories induce RTS-Enriched Categories"

  text\<open>
    Here we show that an RTS-category induces a corresponding RTS-enriched category.
    In order to perform this construction, we will need to have a universe to use
    as the arrow type of the base category \<open>\<^bold>R\<^bold>T\<^bold>S\<close>.  In order to avoid introducing a fixed
    universe, at this point we assume one is given as a parameter.
  \<close>

  locale enriched_category_of_rts_category =
    universe arr_type +
    locally_small_rts_category resid hcomp
  for arr_type :: "'A itself"
  and resid :: "'A resid"  (infix \<open>\\<close> 70)
  and hcomp :: "'A comp"   (infixr \<open>\<star>\<close> 53)
  begin

    sublocale RTS: rtscat arr_type ..

    (* TODO: The composition in RTS is more important here than composition of transitions. *)
    no_notation V.comp       (infixr \<open>\<cdot>\<close> 55)
    no_notation H.in_hom     (\<open>\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>\<close>)
    no_notation RTS.prod     (infixr \<open>\<otimes>\<close> 51)

    (* TODO: Why isn't other notation inherited from rtscat? *)
    notation RTS.in_hom        (\<open>\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>\<close>)
    notation RTS.CMC.tensor    (infixr \<open>\<otimes>\<close> 51)
    notation RTS.CMC.unity     (\<open>\<one>\<close>)
    notation RTS.CMC.assoc     (\<open>\<a>[_, _, _]\<close>)
    notation RTS.CMC.lunit     (\<open>\<l>[_]\<close>)
    notation RTS.CMC.runit     (\<open>\<r>[_]\<close>)

    abbreviation Obj
    where "Obj \<equiv> Collect H.ide"

    definition Hom
    where "Hom a b \<equiv>
           if a \<in> Obj \<and> b \<in> Obj then RTS.mkide (HOM a b) else RTS.null"

    definition Id
    where "Id a \<equiv>
            RTS.mkarr RTS.One.resid (RTS.Rts (Hom a a))
              (\<lambda>t. if RTS.One.arr t
                   then a
                   else ResiduatedTransitionSystem.partial_magma.null (HOM a a))"

    definition Comp
    where "Comp a b c \<equiv>
           RTS.mkarr
             (RTS.Rts (Hom b c \<otimes> Hom a b))
             (RTS.Rts (Hom a c))
             (\<lambda>t. (\<lambda>x. fst x \<star> snd x) (RTS.Unpack (Hom b c) (Hom a b) t))"

    lemma ide_Hom [intro, simp]:
    assumes "a \<in> Obj" and "b \<in> Obj"
    shows "RTS.ide (Hom a b)"
    proof -
      interpret Hom: sub_rts resid \<open>\<lambda>t. H.in_hom t a b\<close>
        using assms sub_rts_HOM by blast
      interpret Hom: extensional_rts Hom.resid
        using Hom.preserves_extensional_rts V.extensional_rts_axioms by blast
      interpret Hom: small_rts Hom.resid
        using assms Hom.arr_char small_homs
        apply unfold_locales
        by (metis Collect_cong mem_Collect_eq)
      show "RTS.ide (Hom a b)"
        unfolding Hom_def
        using assms RTS.ide_mkide Hom.rts_axioms Hom.small_rts_axioms
              Hom.extensional_rts_axioms
        by auto
    qed

    (*
     * TODO: See if this can be simplified.  I have two interpretations that amount to
     * the same thing:  rts (RTS.Rts (Hom a b)) and sub_rts resid \<open>\<lambda>t. H.in_hom t a b\<close>.
     * The problem is, the sub_rts facts are not accessible from the other version.
     *)

    lemma
    assumes "a \<in> Obj" and "b \<in> Obj"
    shows HOM_null_char: "ResiduatedTransitionSystem.partial_magma.null
                            (RTS.Rts (Hom a b)) =
                          null"
    and HOM_arr_char:
          "residuation.arr (RTS.Rts (Hom a b)) t \<longleftrightarrow> H.in_hom t a b"
    proof -
      interpret Hom: sub_rts resid \<open>\<lambda>t. H.in_hom t a b\<close>
        using assms sub_rts_HOM by blast
      show "ResiduatedTransitionSystem.partial_magma.null
              (RTS.Rts (Hom a b)) =
            null"
        using assms Hom_def RTS.bij_mkide(3) Hom.null_char by auto
      show "residuation.arr (RTS.Rts (Hom a b)) t \<longleftrightarrow> H.in_hom t a b"
        unfolding Hom_def
        using assms arr_coincidence Hom.arr_char RTS.bij_mkide(3) by simp
    qed

    lemma Id_in_hom [intro]:
    assumes "a \<in> Obj"
    shows "\<guillemotleft>Id a : \<one> \<rightarrow> Hom a a\<guillemotright>"
    proof -
      interpret Hom: sub_rts resid \<open>\<lambda>t. H.in_hom t a a\<close>
        using assms sub_rts_HOM by blast
      interpret Hom: extensional_rts Hom.resid
        using Hom.preserves_extensional_rts V.extensional_rts_axioms by blast
      interpret Hom: small_rts Hom.resid
        using assms Hom.arr_char small_homs
        apply unfold_locales
        by (metis Collect_cong mem_Collect_eq)
      interpret I: simulation RTS.One.resid \<open>Hom.resid\<close>
                     \<open>\<lambda>t. if RTS.One.arr t then a else Hom.null\<close>
      proof
        show "\<And>t. \<not> RTS.One.arr t \<Longrightarrow>
                      (if RTS.One.arr t then a else Hom.null) = Hom.null"
          by simp
        show 1: "\<And>t u. RTS.One.con t u \<Longrightarrow>
                         Hom.con (if RTS.One.arr t then a else Hom.null)
                                 (if RTS.One.arr u then a else Hom.null)"
          using H.ide_in_hom Hom.arr_char RTS.One.con_implies_arr(1-2) assms
          by auto
        show "\<And>t u. RTS.One.con t u \<Longrightarrow>
                       (if RTS.One.arr (t \\\<^sub>1 u) then a else Hom.null) =
                       Hom.resid
                         (if RTS.One.arr t then a else Hom.null)
                         (if RTS.One.arr u then a else Hom.null)"
          using H.ide_in_hom Hom.resid_def RTS.One.con_implies_arr(1-2)
                V.resid_arr_ide assms obj_implies_sta
          by force
      qed
      show "\<guillemotleft>Id a : \<one> \<rightarrow> Hom a a\<guillemotright>"
      proof
        show 1: "RTS.arr (Id a)"
        proof (unfold Id_def, intro RTS.arr_mkarr)
          show "extensional_rts RTS.One.resid \<and> small_rts RTS.One.resid"
            using RTS.One.is_extensional_rts RTS.One.small_rts_axioms by auto
          show "extensional_rts (RTS.Rts (Hom a a)) \<and>
                  small_rts (RTS.Rts (Hom a a))"
            using assms by auto
          show "simulation (\\\<^sub>1) (RTS.Rts (Hom a a))
                  (\<lambda>t. if RTS.One.arr t then a else Hom.null)"
            unfolding Hom_def
            using assms RTS.bij_mkide(3) I.simulation_axioms by auto
        qed
        show "RTS.dom (Id a) = \<one>"
          using 1 Id_def by (simp add: RTS.unity_agreement)
        show "RTS.cod (Id a) = Hom a a"
          using 1 Id_def assms by force
      qed
    qed

    lemma Id_simps [simp]:
    assumes "a \<in> Obj"
    shows "RTS.arr (Id a)"
    and "RTS.dom (Id a) = \<^bold>\<one>"
    and "RTS.cod (Id a) = Hom a a"
      using assms Id_in_hom RTS.unity_agreement by auto

    lemma Comp_in_hom [intro, simp]:
    assumes "a \<in> Obj" and "b \<in> Obj" and "c \<in> Obj"
    shows "\<guillemotleft>Comp a b c : Hom b c \<otimes> Hom a b \<rightarrow> Hom a c\<guillemotright>"
    proof (unfold Comp_def, intro RTS.in_homI)
      show 0: "RTS.arr (RTS.mkarr
                        (RTS.Rts (Hom b c \<otimes> Hom a b))
                        (RTS.Rts (Hom a c))
                        (\<lambda>t. fst (RTS.Unpack (Hom b c) (Hom a b) t) \<star>
                             snd (RTS.Unpack (Hom b c) (Hom a b) t)))"
      proof (intro RTS.arr_mkarr)
        show "extensional_rts (RTS.Rts (Hom b c \<otimes> Hom a b)) \<and>
                small_rts (RTS.Rts (Hom b c \<otimes> Hom a b))"
          using assms by auto
        show "extensional_rts (RTS.Rts (Hom a c)) \<and>
                small_rts (RTS.Rts (Hom a c))"
          using assms by auto
        show "simulation (RTS.Rts (Hom b c \<otimes> Hom a b)) (RTS.Rts (Hom a c))
                (\<lambda>t. fst (RTS.Unpack (Hom b c) (Hom a b) t) \<star>
                     snd (RTS.Unpack (Hom b c) (Hom a b) t))"
        proof -
          interpret ac: extensional_rts \<open>RTS.Rts (Hom a c)\<close>
            using assms by auto
          interpret bc: extensional_rts \<open>RTS.Rts (Hom b c)\<close>
            using assms by simp
          interpret ab: extensional_rts \<open>RTS.Rts (Hom a b)\<close>
            using assms by simp
          interpret HOM_ab: sub_rts resid \<open>\<lambda>t. H.in_hom t a b\<close>
            using assms sub_rts_HOM by blast
          interpret HOM_bc: sub_rts resid \<open>\<lambda>t. H.in_hom t b c\<close>
            using assms sub_rts_HOM by blast
          interpret HOM_ac: sub_rts resid \<open>\<lambda>t. H.in_hom t a c\<close>
            using assms sub_rts_HOM by blast
          interpret bcxab: extensional_rts \<open>RTS.Rts (Hom b c \<otimes> Hom a b)\<close>
            using assms by auto
          interpret bcXab: product_rts \<open>RTS.Rts (Hom b c)\<close> \<open>RTS.Rts (Hom a b)\<close>
            ..
          interpret U: simulation
                         \<open>RTS.Rts (Hom b c \<otimes> Hom a b)\<close> bcXab.resid
                         \<open>RTS.Unpack (Hom b c) (Hom a b)\<close>
            using assms RTS.simulation_Unpack by simp
          show ?thesis
          proof
            show "\<And>t. \<not> bcxab.arr t \<Longrightarrow>
                           fst (RTS.Unpack (Hom b c) (Hom a b) t) \<star>
                             snd (RTS.Unpack (Hom b c) (Hom a b) t) =
                           ac.null"
              using assms H.null_is_zero(2) HOM_null_char U.simulation_axioms
                    simulation.extensional
              by fastforce
            fix t u
            assume tu: "bcxab.con t u"
            have 1: "HOM_ab.con = ab.con \<and> HOM_bc.con = bc.con \<and>
                       HOM_ac.con = ac.con"
              using assms Hom_def arr_coincidence null_coincidence
                    RTS.bij_mkide(3)
              by auto
            have 2: "H.in_hom (fst (RTS.Unpack (Hom b c) (Hom a b) t)) b c \<and>
                     H.in_hom (snd (RTS.Unpack (Hom b c) (Hom a b) t)) a b \<and>
                     H.in_hom (fst (RTS.Unpack (Hom b c) (Hom a b) u)) b c \<and>
                     H.in_hom (snd (RTS.Unpack (Hom b c) (Hom a b) u)) a b"
              using assms tu bcxab.con_implies_arr Hom_def
                    U.preserves_reflects_arr bcXab.arr_char HOM_ab.arr_char
                    HOM_bc.arr_char RTS.bij_mkide(3)
              by auto
            hence 3: "H.in_hom (fst (RTS.Unpack (Hom b c) (Hom a b) t) \<star>
                                snd (RTS.Unpack (Hom b c) (Hom a b) t))
                        a c \<and>
                      H.in_hom (fst (RTS.Unpack (Hom b c) (Hom a b) u) \<star>
                                snd (RTS.Unpack (Hom b c) (Hom a b) u))
                        a c"
              using assms arr_coincidence by blast
            have 4: "V.con (fst (RTS.Unpack (Hom b c) (Hom a b) t))
                        (fst (RTS.Unpack (Hom b c) (Hom a b) u)) \<and>
                      V.con (snd (RTS.Unpack (Hom b c) (Hom a b) t))
                        (snd (RTS.Unpack (Hom b c) (Hom a b) u))"
              using tu 1 2 3 bcXab.con_char HOM_bc.con_char HOM_ab.con_char
                    U.preserves_con
              by auto
            hence 5: "VV.con
                        (RTS.Unpack (Hom b c) (Hom a b) t)
                        (RTS.Unpack (Hom b c) (Hom a b) u)"
              using 2 3 bcXab.con_char VV.con_char Hom_def arr_coincidence
                    null_coincidence
              by fast
            hence 6: "fst (RTS.Unpack (Hom b c) (Hom a b) t) \<star>
                        snd (RTS.Unpack (Hom b c) (Hom a b) t) \<frown>
                      fst (RTS.Unpack (Hom b c) (Hom a b) u) \<star>
                        snd (RTS.Unpack (Hom b c) (Hom a b) u)"
              using H.preserves_con VV.con_implies_arr by auto
            thus "ac.con
                    (fst (RTS.Unpack (Hom b c) (Hom a b) t) \<star>
                       snd (RTS.Unpack (Hom b c) (Hom a b) t))
                    (fst (RTS.Unpack (Hom b c) (Hom a b) u) \<star>
                       snd (RTS.Unpack (Hom b c) (Hom a b) u))"
              using 1 3 HOM_ac.con_char by simp
            show "fst (RTS.Unpack (Hom b c) (Hom a b)
                         (RTS.Rts (Hom b c \<otimes> Hom a b) t u)) \<star>
                    snd (RTS.Unpack (Hom b c) (Hom a b)
                           (RTS.Rts (Hom b c \<otimes> Hom a b) t u)) =
                  RTS.Rts (Hom a c)
                    (fst (RTS.Unpack (Hom b c) (Hom a b) t) \<star>
                       snd (RTS.Unpack (Hom b c) (Hom a b) t))
                    (fst (RTS.Unpack (Hom b c) (Hom a b) u) \<star>
                       snd (RTS.Unpack (Hom b c) (Hom a b) u))"
            proof -
              have "RTS.Rts (Hom a c)
                      (fst (RTS.Unpack (Hom b c) (Hom a b) t) \<star>
                         snd (RTS.Unpack (Hom b c) (Hom a b) t))
                      (fst (RTS.Unpack (Hom b c) (Hom a b) u) \<star>
                         snd (RTS.Unpack (Hom b c) (Hom a b) u)) =
                    (fst (RTS.Unpack (Hom b c) (Hom a b) t) \<star>
                       snd (RTS.Unpack (Hom b c) (Hom a b) t)) \\
                    (fst (RTS.Unpack (Hom b c) (Hom a b) u) \<star>
                       snd (RTS.Unpack (Hom b c) (Hom a b) u))"
                using assms 3 6 Hom_def HOM_ac.resid_def RTS.bij_mkide(3)
                by simp
              also have "... = fst (VV.resid
                                      (RTS.Unpack (Hom b c) (Hom a b) t)
                                      (RTS.Unpack (Hom b c) (Hom a b) u)) \<star>
                                 snd (VV.resid
                                        (RTS.Unpack (Hom b c) (Hom a b) t)
                                        (RTS.Unpack (Hom b c) (Hom a b) u))"
                using 5 VV.con_implies_arr H.preserves_resid by simp
              also have "... = fst (bcXab.resid
                                     (RTS.Unpack (Hom b c) (Hom a b) t)
                                     (RTS.Unpack (Hom b c) (Hom a b) u)) \<star>
                                 snd (bcXab.resid
                                        (RTS.Unpack (Hom b c) (Hom a b) t)
                                        (RTS.Unpack (Hom b c) (Hom a b) u))"
              proof -
                have "RTS.Rts (Hom b c)
                        (fst (RTS.Unpack (Hom b c) (Hom a b) t))
                        (fst (RTS.Unpack (Hom b c) (Hom a b) u)) =
                      fst (RTS.Unpack (Hom b c) (Hom a b) t) \\
                        fst (RTS.Unpack (Hom b c) (Hom a b) u)"
                  using 2 Hom_def RTS.bij_mkide(3)
                        HOM_bc.resid_def
                          [of "fst (RTS.Unpack (Hom b c) (Hom a b) t)"
                              "fst (RTS.Unpack (Hom b c) (Hom a b) u)"]
                  apply auto[1]
                  by auto
                moreover have "RTS.Rts (Hom a b)
                                 (snd (RTS.Unpack (Hom b c) (Hom a b) t))
                                 (snd (RTS.Unpack (Hom b c) (Hom a b) u)) =
                               snd (RTS.Unpack (Hom b c) (Hom a b) t) \\
                                 snd (RTS.Unpack (Hom b c) (Hom a b) u)"
                  using 2 Hom_def RTS.bij_mkide(3)
                        HOM_ab.resid_def
                          [of "snd (RTS.Unpack (Hom b c) (Hom a b) t)"
                              "snd (RTS.Unpack (Hom b c) (Hom a b) u)"]
                  apply auto[1]
                  by auto
                ultimately show ?thesis
                  using tu 2 4 bcXab.resid_def bcXab.con_char VV.resid_def
                        U.preserves_con
                  apply auto[1]
                  by fastforce+
              qed
              also have "... = fst (RTS.Unpack (Hom b c) (Hom a b)
                                      (RTS.Rts (Hom b c \<otimes> Hom a b) t u)) \<star>
                                 snd (RTS.Unpack (Hom b c) (Hom a b)
                                        (RTS.Rts (Hom b c \<otimes> Hom a b) t u))"
                using tu U.preserves_resid by simp
              finally show ?thesis by simp
            qed
          qed
        qed
      qed
      show "RTS.dom
              (RTS.mkarr (RTS.Rts (Hom b c \<otimes> Hom a b)) (RTS.Rts (Hom a c))
                         (\<lambda>t. fst (RTS.Unpack (Hom b c) (Hom a b) t) \<star>
                                snd (RTS.Unpack (Hom b c) (Hom a b) t))) =
            Hom b c \<otimes> Hom a b"
        using assms 0 by auto
      show "RTS.cod
              (RTS.mkarr (RTS.Rts (Hom b c \<otimes> Hom a b)) (RTS.Rts (Hom a c))
                         (\<lambda>t. fst (RTS.Unpack (Hom b c) (Hom a b) t) \<star>
                                snd (RTS.Unpack (Hom b c) (Hom a b) t))) =
            Hom a c"
        using assms 0 by auto
    qed

    lemma Comp_simps [simp]:
    assumes "a \<in> Obj" and "b \<in> Obj" and "c \<in> Obj"
    shows "RTS.arr (Comp a b c)"
    and "RTS.dom (Comp a b c) = Hom b c \<otimes> Hom a b"
    and "RTS.cod (Comp a b c) = Hom a c"
      using assms Comp_in_hom RTS.in_homE by auto

    lemma Map_Comp_Pack:
    assumes "a \<in> Obj" and "b \<in> Obj" and "c \<in> Obj"
    and "residuation.arr
            (product_rts.resid (RTS.Rts (Hom b c)) (RTS.Rts (Hom a b))) x"
    shows "RTS.Map (Comp a b c) (RTS.Pack (Hom b c) (Hom a b) x) =
           fst x \<star> snd x"
      using assms Comp_def RTS.bij_mkarr(3) by simp

    sublocale rts_enriched_category arr_type Obj Hom Id Comp
    proof
      show "\<And>a b. \<lbrakk>a \<in> Obj; b \<in> Obj\<rbrakk> \<Longrightarrow> RTS.ide (Hom a b)"
        by blast
      show "\<And>a. a \<in> Obj \<Longrightarrow> \<guillemotleft>Id a : \<one> \<rightarrow> Hom a a\<guillemotright>"
        using Id_in_hom RTS.unity_agreement by auto
      show "\<And>a b c. \<lbrakk>a \<in> Obj; b \<in> Obj; c \<in> Obj\<rbrakk> \<Longrightarrow>
                       \<guillemotleft>Comp a b c : Hom b c \<otimes> Hom a b \<rightarrow> Hom a c\<guillemotright>"
        using Comp_in_hom by auto

      fix a b
      assume a: "a \<in> Obj" and b: "b \<in> Obj"
      interpret ab: extensional_rts \<open>RTS.Rts (Hom a b)\<close>
        using a b by simp
      interpret aa: extensional_rts \<open>RTS.Rts (Hom a a)\<close>
        using a by simp
      interpret bb: extensional_rts \<open>RTS.Rts (Hom b b)\<close>
        using b by simp
      interpret abXaa: product_rts \<open>RTS.Rts (Hom a b)\<close> \<open>RTS.Rts (Hom a a)\<close> ..
      interpret bbXab: product_rts \<open>RTS.Rts (Hom b b)\<close> \<open>RTS.Rts (Hom a b)\<close> ..
      interpret ab: simulation \<open>RTS.Rts (Hom a b)\<close> \<open>RTS.Rts (Hom a b)\<close>
                      \<open>RTS.Map (Hom a b)\<close>
        using a b ide_Hom RTS.arrD
        by (metis (no_types, lifting) RTS.ide_char)
      interpret I: simulation RTS.One.resid \<open>RTS.Rts (Hom a a)\<close>
                     \<open>RTS.Map (Id a)\<close>
        using a ide_Hom Id_in_hom RTS.ide_char
        by (metis (no_types, lifting) RTS.Rts_one RTS.arrD(3) RTS.in_homE
            RTS.unity_agreement)
      interpret Ib: simulation RTS.One.resid \<open>RTS.Rts (Hom b b)\<close>
                      \<open>RTS.Map (Id b)\<close>
        using b ide_Hom Id_in_hom RTS.ide_char
        by (metis (no_types, lifting) RTS.Rts_one RTS.arrD(3) RTS.in_homE
            RTS.unity_agreement)
      interpret abXI: product_simulation
                        \<open>RTS.Rts (Hom a b)\<close> RTS.One.resid
                        \<open>RTS.Rts (Hom a b)\<close> \<open>RTS.Rts(Hom a a)\<close>
                        \<open>RTS.Map (Hom a b)\<close> \<open>RTS.Map (Id a)\<close>
        ..
      interpret IXab: product_simulation
                        RTS.One.resid \<open>RTS.Rts (Hom a b)\<close>
                        \<open>RTS.Rts (Hom b b)\<close> \<open>RTS.Rts (Hom a b)\<close>
                        \<open>RTS.Map (Id b)\<close> \<open>RTS.Map (Hom a b)\<close>
        ..
      interpret abxone: extensional_rts \<open>RTS.Rts (Hom a b \<otimes> \<one>)\<close>
        using a b by auto
      interpret onexab: extensional_rts \<open>RTS.Rts (\<one> \<otimes> Hom a b)\<close>
        using a b by auto
      interpret PU_abXI: inverse_simulations
                           \<open>RTS.Rts (Hom a b \<otimes> \<one>)\<close> \<open>abXI.A1xA0.resid\<close>
                           \<open>RTS.Pack (Hom a b) \<one>\<close> \<open>RTS.Unpack (Hom a b) \<one>\<close>
        using a b RTS.ide_one
              RTS.inverse_simulations_Pack_Unpack [of "Hom a b" \<one>]
        by simp
      interpret PU_IXab: inverse_simulations
                           \<open>RTS.Rts (\<one> \<otimes> Hom a b)\<close> \<open>IXab.A1xA0.resid\<close>
                           \<open>RTS.Pack \<one> (Hom a b)\<close> \<open>RTS.Unpack \<one> (Hom a b)\<close>
        using a b RTS.ide_one
              RTS.inverse_simulations_Pack_Unpack [of \<one> "Hom a b"]
        by simp
      interpret PU_abXaa: inverse_simulations
                            \<open>RTS.Rts (Hom a b \<otimes> Hom a a)\<close> abXaa.resid
                            \<open>RTS.Pack (Hom a b) (Hom a a)\<close>
                            \<open>RTS.Unpack (Hom a b) (Hom a a)\<close>
        using a b RTS.ide_one
              RTS.inverse_simulations_Pack_Unpack [of "Hom a b" "Hom a a"]
        by simp
      interpret PU_bbXab: inverse_simulations
                            \<open>RTS.Rts (Hom b b \<otimes> Hom a b)\<close> bbXab.resid
                            \<open>RTS.Pack (Hom b b) (Hom a b)\<close>
                            \<open>RTS.Unpack (Hom b b) (Hom a b)\<close>
        using a b RTS.ide_one
              RTS.inverse_simulations_Pack_Unpack [of "Hom b b" "Hom a b"]
        by simp

      show "Comp a a b \<cdot> (Hom a b \<otimes> Id a) = \<r>[Hom a b]"
      proof (intro RTS.arr_eqI)
        show 1: "RTS.par (Comp a a b \<cdot> (Hom a b \<otimes> Id a)) \<r>[Hom a b]"
          using a b Id_in_hom by fastforce+
        show "RTS.Map (Comp a a b \<cdot> (Hom a b \<otimes> Id a)) = RTS.Map \<r>[Hom a b]"
        proof -
          have "RTS.Map (Comp a a b \<cdot> (Hom a b \<otimes> Id a)) =
                RTS.Map (Comp a a b) \<circ> RTS.Map (Hom a b \<otimes> Id a)"
            using a b 1 Comp_in_hom Id_in_hom RTS.Map_comp by blast
          also have "... = (\<lambda>t. fst ((RTS.Unpack (Hom a b) (Hom a a) \<circ>
                                        RTS.Pack (Hom a b) (Hom a a) \<circ>
                                           abXI.map \<circ>
                                             RTS.Unpack (Hom a b) \<one>) t)
                                \<star>
                                snd ((RTS.Unpack (Hom a b) (Hom a a) \<circ>
                                        RTS.Pack (Hom a b) (Hom a a) \<circ>
                                          abXI.map \<circ>
                                            RTS.Unpack (Hom a b) \<one>) t))"
            using a b ide_Hom Id_in_hom Comp_in_hom Comp_def RTS.Map_prod
                  RTS.Map_mkarr RTS.tensor_agreement RTS.bij_mkarr(3)
                  RTS.unity_agreement
            by auto
          also have "... = (\<lambda>t. fst ((I abXaa.resid \<circ> abXI.map \<circ>
                                        RTS.Unpack (Hom a b) \<one>) t) \<star>
                                  snd ((I abXaa.resid \<circ> abXI.map \<circ>
                                          RTS.Unpack (Hom a b) \<one>) t))"
            using PU_abXaa.inv by auto
          also have "... = RTS.Map \<r>[Hom a b]"
          proof
            fix t
            show "fst ((I abXaa.resid \<circ> abXI.map \<circ>
                          RTS.Unpack (Hom a b) \<one>) t) \<star>
                    snd ((I abXaa.resid \<circ> abXI.map \<circ>
                            RTS.Unpack (Hom a b) \<one>) t) =
                  RTS.Map \<r>[Hom a b] t"
            proof (cases "abxone.arr t")
              show "\<not> abxone.arr t \<Longrightarrow> ?thesis"
              proof -
                assume t: "\<not> abxone.arr t"
                have "fst ((I abXaa.resid \<circ> abXI.map \<circ>
                              RTS.Unpack (Hom a b) \<one>) t) \<star>
                      snd ((I abXaa.resid \<circ> abXI.map \<circ>
                              RTS.Unpack (Hom a b) \<one>) t) =
                      null"
                  using a b t 1 PU_abXI.G.extensional abXI.extensional
                        abXI.A1xA0.P\<^sub>1.extensional H.null_is_zero(2)
                        HOM_null_char null_coincidence
                  by simp
                also have "... = RTS.Map \<r>[Hom a b] t"
                proof -
                  interpret R: simulation \<open>RTS.Rts (Hom a b \<otimes> \<one>)\<close>
                    \<open>RTS.Rts (Hom a b)\<close> \<open>RTS.Map \<r>[Hom a b]\<close>
                    using a b 1 ide_Hom RTS.arrD(3)
                    by (metis (no_types, lifting) RTS.CMC.cod_runit
                        RTS.CMC.dom_runit)
                  show ?thesis
                    using a b t R.extensional HOM_null_char by simp
                qed
                finally show ?thesis by blast
              qed
              assume t: "abxone.arr t"
              have "(I abXaa.resid \<circ> abXI.map \<circ> RTS.Unpack (Hom a b) \<one>) t =
                    (RTS.Map \<r>[Hom a b] t, a)"
              proof -
                have "(I abXaa.resid \<circ> abXI.map \<circ> RTS.Unpack (Hom a b) \<one>) t =
                      I abXaa.resid (abXI.map (RTS.Unpack (Hom a b) \<one> t))"
                  by auto
                also have "... = abXI.map (RTS.Unpack (Hom a b) \<one> t)"
                  using a b t abXI.preserves_reflects_arr
                        PU_abXI.G.preserves_reflects_arr
                  by simp
                also have "... = (fst (RTS.Unpack (Hom a b) \<one> t),
                                  RTS.Map (Id a)
                                    (snd (RTS.Unpack (Hom a b) \<one> t)))"
                  using a b t PU_abXI.G.preserves_reflects_arr
                        RTS.Map_ide
                        abXI.map_simp [of "fst (RTS.Unpack (Hom a b) \<one> t)"
                                          "snd (RTS.Unpack (Hom a b) \<one> t)"]
                  by auto
                also have "... = (fst (RTS.Unpack (Hom a b) \<one> t), a)"
                  unfolding Id_def
                  using a b t PU_abXI.G.preserves_reflects_arr
                        Id_def RTS.bij_mkarr(3) RTS.ide_one
                        RTS.One.is_extensional_rts RTS.One.small_rts_axioms
                  by auto
                also have "... = (RTS.Map \<r>[Hom a b] t, a)"
                  using a b t RTS.runit_agreement RTS.Map_runit
                        abXI.A1xA0.P\<^sub>1_def RTS.unity_agreement
                        PU_abXI.G.preserves_reflects_arr
                  by auto
                finally show ?thesis by blast
              qed
              moreover have "H.in_hom (RTS.Map \<r>[Hom a b] t) a b"
                using a b t RTS.Map_runit PU_abXI.G.preserves_reflects_arr
                      HOM_arr_char
                        [of a b "(abXI.A1xA0.P\<^sub>1 \<circ> RTS.Unpack (Hom a b) \<one>) t"]
                      RTS.runit_agreement RTS.unity_agreement
                by auto
              ultimately show ?thesis
                using a b H.comp_arr_dom by auto
            qed
          qed
          finally show ?thesis by blast
        qed
      qed

      show "Comp a b b \<cdot> (Id b \<otimes> Hom a b) = \<l>[Hom a b]"
      proof (intro RTS.arr_eqI)
        show 1: "RTS.par (Comp a b b \<cdot> (Id b \<otimes> Hom a b)) \<l>[Hom a b]"
          using a b Id_in_hom [of b] by auto
        show "RTS.Map (Comp a b b \<cdot> (Id b \<otimes> Hom a b)) = RTS.Map \<l>[Hom a b]"
        proof -
          have "RTS.Map (Comp a b b \<cdot> (Id b \<otimes> Hom a b)) =
                RTS.Map (Comp a b b) \<circ> RTS.Map (Id b \<otimes> Hom a b)"
            using a b 1 Comp_in_hom Id_in_hom RTS.Map_comp by blast
          also have "... = (\<lambda>t. fst (RTS.Unpack (Hom b b) (Hom a b) t) \<star>
                                  snd (RTS.Unpack (Hom b b) (Hom a b) t)) \<circ>
                             (RTS.Pack (Hom b b) (Hom a b) \<circ>
                                IXab.map \<circ>
                                  RTS.Unpack \<one> (Hom a b))"
            using a b ide_Hom Id_in_hom Comp_in_hom [of a b b]
                  Comp_def RTS.Map_prod RTS.Map_mkarr RTS.tensor_agreement
                  RTS.unity_agreement
            by auto
          also have "... = (\<lambda>t. fst ((RTS.Unpack (Hom b b) (Hom a b) \<circ>
                                        RTS.Pack (Hom b b) (Hom a b) \<circ>
                                          IXab.map \<circ>
                                            RTS.Unpack \<one> (Hom a b)) t)
                                \<star>
                                snd ((RTS.Unpack (Hom b b) (Hom a b) \<circ>
                                        RTS.Pack (Hom b b) (Hom a b) \<circ>
                                          IXab.map \<circ>
                                            RTS.Unpack \<one> (Hom a b)) t))"
            by auto
          also have "... = (\<lambda>t. fst ((I bbXab.resid \<circ> IXab.map \<circ>
                                        RTS.Unpack \<one> (Hom a b)) t) \<star>
                                  snd ((I bbXab.resid \<circ> IXab.map \<circ>
                                          RTS.Unpack \<one> (Hom a b)) t))"
            using PU_bbXab.inv by auto
          also have "... = RTS.Map \<l>[Hom a b]"
          proof
            fix t
            show "fst ((I bbXab.resid \<circ> IXab.map \<circ>
                          RTS.Unpack \<one> (Hom a b)) t) \<star>
                    snd ((I bbXab.resid \<circ> IXab.map \<circ>
                            RTS.Unpack \<one> (Hom a b)) t) =
                  RTS.Map \<l>[Hom a b] t"
            proof (cases "onexab.arr t")
              show "\<not> onexab.arr t \<Longrightarrow> ?thesis"
              proof -
                assume t: "\<not> onexab.arr t"
                have "fst ((I bbXab.resid \<circ> IXab.map \<circ> RTS.Unpack \<one> (Hom a b)) t) \<star>
                      snd ((I bbXab.resid \<circ> IXab.map \<circ> RTS.Unpack \<one> (Hom a b)) t) =
                      null"
                  using a b t 1 PU_IXab.G.extensional IXab.extensional
                        IXab.A1xA0.P\<^sub>0.extensional HOM_null_char
                  apply auto[1]
                  by (metis H.null_is_zero(2) null_coincidence)+
                also have "... = RTS.Map \<l>[Hom a b] t"
                proof -
                  interpret L: simulation
                                 \<open>RTS.Rts (\<one> \<otimes> Hom a b)\<close> \<open>RTS.Rts (Hom a b)\<close>
                                 \<open>RTS.Map \<l>[Hom a b]\<close>
                    using a b t 1 RTS.arrD(3) [of "\<l>[Hom a b]"] by force
                  show ?thesis
                    using t L.extensional HOM_null_char a b by force
                qed
                finally show ?thesis by blast
              qed
              assume t: "onexab.arr t"
              have "(I bbXab.resid \<circ> IXab.map \<circ> RTS.Unpack \<one> (Hom a b)) t =
                    (b, RTS.Map \<l>[Hom a b] t)"
              proof -
                have "(I bbXab.resid \<circ> IXab.map \<circ> RTS.Unpack \<one> (Hom a b)) t =
                      I bbXab.resid (IXab.map (RTS.Unpack \<one> (Hom a b) t))"
                  by auto
                also have "... = IXab.map (RTS.Unpack \<one> (Hom a b) t)"
                  using a b t IXab.preserves_reflects_arr PU_IXab.G.preserves_reflects_arr
                  by simp
                also have "... = (RTS.Map (Id b) (fst (RTS.Unpack \<one> (Hom a b) t)),
                                  snd (RTS.Unpack \<one> (Hom a b) t))"
                  using a b t PU_IXab.G.preserves_reflects_arr RTS.Map_ide
                        IXab.map_simp
                          [of "fst (RTS.Unpack \<one> (Hom a b) t)"
                              "snd (RTS.Unpack \<one> (Hom a b) t)"]
                  by auto
                also have "... = (b, snd (RTS.Unpack \<one> (Hom a b) t))"
                  unfolding Id_def
                  using a b t PU_IXab.G.preserves_reflects_arr Id_def
                        RTS.One.is_extensional_rts
                        RTS.One.small_rts_axioms RTS.bij_mkarr(3)
                  by auto
                also have "... = (b, RTS.Map \<l>[Hom a b] t)"
                  using a b t RTS.lunit_agreement RTS.Map_lunit
                        IXab.A1xA0.P\<^sub>0_def RTS.unity_agreement
                        PU_IXab.G.preserves_reflects_arr
                  by auto
                finally show ?thesis by blast
              qed
              moreover have "H.in_hom (RTS.Map \<l>[Hom a b] t) a b"
                using a b t RTS.Map_lunit
                      RTS.lunit_agreement RTS.unity_agreement
                      PU_IXab.G.preserves_reflects_arr
                      HOM_arr_char
                        [of a b "(IXab.A1xA0.P\<^sub>0 \<circ> RTS.Unpack \<one> (Hom a b)) t"]
                by auto
              ultimately show ?thesis
                using a b H.comp_cod_arr by auto
            qed
          qed
          finally show ?thesis by blast
        qed
      qed
      next
      show "\<And>a b c d. \<lbrakk>a \<in> Obj; b \<in> Obj; c \<in> Obj; d \<in> Obj\<rbrakk>
                         \<Longrightarrow> Comp a b d \<cdot> (Comp b c d \<otimes> Hom a b) =
                             Comp a c d \<cdot> (Hom c d \<otimes> Comp a b c) \<cdot>
                               \<a>[Hom c d, Hom b c, Hom a b]"
      proof -
        fix a b c d
        assume a: "a \<in> Obj" and b: "b \<in> Obj" and c: "c \<in> Obj" and d: "d \<in> Obj"
        interpret ab: extensional_rts \<open>RTS.Rts (Hom a b)\<close>
          using a b by fastforce
        interpret bc: extensional_rts \<open>RTS.Rts (Hom b c)\<close>
          using b c by fastforce
        interpret cd: extensional_rts \<open>RTS.Rts (Hom c d)\<close>
          using c d by fastforce
        interpret ac: extensional_rts \<open>RTS.Rts (Hom a c)\<close>
          using a c by fastforce
        interpret bd: extensional_rts \<open>RTS.Rts (Hom b d)\<close>
          using b d by fastforce
        interpret bcxab: extensional_rts
                           \<open>RTS.Rts (RTS.dom (Hom b c \<otimes> Hom a b))\<close>
          using a b c by auto
        interpret cdxbc: rts \<open>RTS.Rts (RTS.dom (Hom c d \<otimes> Hom b c))\<close>
          using b c d ide_Hom RTS.ide_char RTS.arrD extensional_rts_def
          by (metis RTS.CMC.tensor_preserves_ide)
        interpret cdxbc_x_ab:
                    rts \<open>RTS.Rts (RTS.dom ((Hom c d \<otimes> Hom b c) \<otimes> Hom a b))\<close>
          using a b c d extensional_rts_def by fastforce
        interpret cd_X_bcxab: product_rts
                                \<open>RTS.Rts (Hom c d)\<close>
                                \<open>RTS.Rts (RTS.dom (Hom b c \<otimes> Hom a b))\<close>
          ..
        interpret cdxbc_X_ab: product_rts
                                \<open>RTS.Rts (RTS.dom (Hom c d \<otimes> Hom b c))\<close>
                                \<open>RTS.Rts (Hom a b)\<close>
          ..
        interpret bcXab: product_rts \<open>RTS.Rts (Hom b c)\<close> \<open>RTS.Rts (Hom a b)\<close> ..
        interpret cdXbc: product_rts \<open>RTS.Rts (Hom c d)\<close> \<open>RTS.Rts (Hom b c)\<close> ..
        interpret cd_X_bcXab: product_rts \<open>RTS.Rts (Hom c d)\<close> bcXab.resid ..
        interpret cdXbc_X_ab: product_rts cdXbc.resid \<open>RTS.Rts (Hom a b)\<close> ..
        interpret Icd: simulation \<open>RTS.Rts (Hom c d)\<close> \<open>RTS.Rts (Hom c d)\<close>
                         \<open>RTS.Map (Hom c d)\<close>
          by (metis RTS.arrD(3) RTS.ide_char c d ide_Hom)
        interpret Iab: simulation \<open>RTS.Rts (Hom a b)\<close> \<open>RTS.Rts (Hom a b)\<close>
                         \<open>RTS.Map (Hom a b)\<close>
          by (metis RTS.arrD(3) RTS.ideD(1-3) a b ide_Hom)
        interpret Cabc: simulation
                          \<open>RTS.Rts (RTS.dom (Hom b c \<otimes> Hom a b))\<close>
                          \<open>RTS.Rts (Hom a c)\<close>
                          \<open>RTS.Map (Comp a b c)\<close>
          by (metis (no_types, lifting) Comp_in_hom
              RTS.CMC.tensor_preserves_ide RTS.arrD(3) RTS.ideD(2)
              RTS.in_homE a b c ide_Hom)
        interpret Cbcd: simulation
                          \<open>RTS.Rts (RTS.dom (Hom c d \<otimes> Hom b c))\<close>
                          \<open>RTS.Rts (Hom b d)\<close>
                          \<open>RTS.Map (Comp b c d)\<close>
          by (metis (no_types, lifting) Comp_in_hom
              RTS.CMC.tensor_preserves_ide RTS.arrD(3) RTS.ideD(2)
              RTS.in_homE b c d ide_Hom)
        interpret Cabd: simulation
                          \<open>RTS.Rts (RTS.dom (Hom b d \<otimes> Hom a b))\<close>
                          \<open>RTS.Rts (Hom a d)\<close>
                          \<open>RTS.Map (Comp a b d)\<close>
          by (metis (no_types, lifting) Comp_in_hom
              RTS.CMC.tensor_preserves_ide RTS.arrD(3) RTS.ideD(2)
              RTS.in_homE a b d ide_Hom)
        interpret IcdXCabc: product_simulation
                             \<open>RTS.Rts (Hom c d)\<close>
                             \<open>RTS.Rts (RTS.dom (Hom b c \<otimes> Hom a b))\<close>
                             \<open>RTS.Rts (Hom c d)\<close> \<open>RTS.Rts (Hom a c)\<close>
                             \<open>RTS.Map (Hom c d)\<close> \<open>RTS.Map (Comp a b c)\<close>
          ..
        interpret CbcdXIab: product_simulation
                             \<open>RTS.Rts (RTS.dom (Hom c d \<otimes> Hom b c))\<close>
                             \<open>RTS.Rts (Hom a b)\<close>
                             \<open>RTS.Rts (Hom b d)\<close> \<open>RTS.Rts (Hom a b)\<close>
                             \<open>RTS.Map (Comp b c d)\<close> \<open>RTS.Map (Hom a b)\<close>
          ..
        interpret PU_bcXab: inverse_simulations
                              \<open>RTS.Rts (RTS.dom (Hom b c \<otimes> Hom a b))\<close>
                              bcXab.resid
                              \<open>RTS.Pack (Hom b c) (Hom a b)\<close>
                              \<open>RTS.Unpack (Hom b c) (Hom a b)\<close>
          using a b c RTS.inverse_simulations_Pack_Unpack by simp
        interpret PU_bdXab: inverse_simulations
                              \<open>RTS.Rts (RTS.dom (Hom b d \<otimes> Hom a b))\<close>
                              CbcdXIab.B1xB0.resid
                              \<open>RTS.Pack (Hom b d) (Hom a b)\<close>
                              \<open>RTS.Unpack (Hom b d) (Hom a b)\<close>
          using a b c d RTS.inverse_simulations_Pack_Unpack by simp
        interpret PU_cdXac: inverse_simulations
                              \<open>RTS.Rts (RTS.dom (Hom c d \<otimes> Hom a c))\<close>
                              IcdXCabc.B1xB0.resid
                              \<open>RTS.Pack (Hom c d) (Hom a c)\<close>
                              \<open>RTS.Unpack (Hom c d) (Hom a c)\<close>
          using a c d RTS.inverse_simulations_Pack_Unpack by simp
         interpret PU_cdXbc: inverse_simulations
                              \<open>RTS.Rts (RTS.dom (Hom c d \<otimes> Hom b c))\<close>
                              cdXbc.resid
                              \<open>RTS.Pack (Hom c d) (Hom b c)\<close>
                              \<open>RTS.Unpack (Hom c d) (Hom b c)\<close>
          using b c d RTS.inverse_simulations_Pack_Unpack by simp
        interpret PU_cd_X_bcxab: inverse_simulations
                                   \<open>RTS.Rts
                                      (RTS.dom (Hom c d \<otimes> Hom b c \<otimes> Hom a b))\<close>
                                   cd_X_bcxab.resid
                                   \<open>RTS.Pack (Hom c d) (Hom b c \<otimes> Hom a b)\<close>
                                   \<open>RTS.Unpack (Hom c d) (Hom b c \<otimes> Hom a b)\<close>
          using a b c d RTS.inverse_simulations_Pack_Unpack by simp
        interpret PU_cdxbc_X_ab: inverse_simulations
                                   \<open>RTS.Rts
                                      (RTS.dom ((Hom c d \<otimes> Hom b c) \<otimes> Hom a b))\<close>
                                   cdxbc_X_ab.resid
                                   \<open>RTS.Pack (Hom c d \<otimes> Hom b c) (Hom a b)\<close>
                                   \<open>RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b)\<close>
          using a b c d RTS.inverse_simulations_Pack_Unpack by simp
        interpret Ucdxbc_X_Iab: product_simulation
                                  \<open>RTS.Rts (RTS.dom (Hom c d \<otimes> Hom b c))\<close>
                                  \<open>RTS.Rts (Hom a b)\<close>
                                  cdXbc.resid \<open>RTS.Rts (Hom a b)\<close>
                                  \<open>RTS.Unpack (Hom c d) (Hom b c)\<close>
                                  \<open>RTS.Map (Hom a b)\<close>
          ..
        interpret Icd_X_Pbcxab: product_simulation
                                  \<open>RTS.Rts (Hom c d)\<close> bcXab.resid
                                  \<open>RTS.Rts (Hom c d)\<close>
                                  \<open>RTS.Rts (RTS.dom (Hom b c \<otimes> Hom a b))\<close>
                                  \<open>RTS.Map (Hom c d)\<close> \<open>RTS.Pack (Hom b c) (Hom a b)\<close>
          ..
        show "Comp a b d \<cdot> (Comp b c d \<otimes> Hom a b) =
              Comp a c d \<cdot> (Hom c d \<otimes> Comp a b c) \<cdot> \<a>[Hom c d, Hom b c, Hom a b]"
        proof (intro RTS.arr_eqI)
          show 1: "RTS.par (Comp a b d \<cdot> (Comp b c d \<otimes> Hom a b))
                           (Comp a c d \<cdot> (Hom c d \<otimes> Comp a b c) \<cdot>
                              \<a>[Hom c d, Hom b c, Hom a b])"
            using a b c d by auto
          show "RTS.Map (Comp a b d \<cdot> (Comp b c d \<otimes> Hom a b)) =
                RTS.Map (Comp a c d \<cdot> (Hom c d \<otimes> Comp a b c) \<cdot>
                           \<a>[Hom c d, Hom b c, Hom a b])"
          proof
            fix x
            show "RTS.Map (Comp a b d \<cdot> (Comp b c d \<otimes> Hom a b)) x =
                  RTS.Map (Comp a c d \<cdot> (Hom c d \<otimes> Comp a b c) \<cdot>
                             \<a>[Hom c d, Hom b c, Hom a b]) x"
            proof (cases "cdxbc_x_ab.arr x")
              assume x: "\<not> cdxbc_x_ab.arr x"
              show ?thesis
              proof -
                interpret L: simulation
                               \<open>RTS.Dom ((Hom c d \<otimes> Hom b c) \<otimes> Hom a b)\<close>
                               \<open>RTS.Rts (Hom a d)\<close>
                               \<open>RTS.Map (Comp a b d \<cdot> (Comp b c d \<otimes> Hom a b))\<close>
                  using a b c d 1
                        RTS.arrD(3) [of "Comp a b d \<cdot> (Comp b c d \<otimes> Hom a b)"]
                  by auto
                interpret R: simulation
                               \<open>RTS.Rts (RTS.dom ((Hom c d \<otimes> Hom b c) \<otimes> Hom a b))\<close>
                               \<open>RTS.Rts (Hom a d)\<close>
                               \<open>RTS.Map (Comp a c d \<cdot> (Hom c d \<otimes> Comp a b c) \<cdot>
                                           \<a>[Hom c d, Hom b c, Hom a b])\<close>
                  using a b c d 1
                        RTS.arrD(3)
                          [of "Comp a c d \<cdot> (Hom c d \<otimes> Comp a b c) \<cdot>
                                 \<a>[Hom c d, Hom b c, Hom a b]"]
                  by auto
                show ?thesis
                  using x L.extensional R.extensional by simp
              qed
              next
              assume x: "cdxbc_x_ab.arr x"
              let ?w = "RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x"
              let ?x = "RTS.Unpack (Hom c d) (Hom b c) (fst ?w)"
              let ?y = "snd ?w"
              have fst_x: "cd.arr (fst ?x)"
                using cdXbc.arr_char cdxbc_X_ab.arr_char x by blast
              have snd_x: "bc.arr (snd ?x)"
                using cdXbc.arr_char cdxbc_X_ab.arr_char x by blast
              have snd_w: "ab.arr (snd ?w)"
                using cdxbc_X_ab.arr_char x by blast
              show ?thesis
              proof -
                have "RTS.Map (Comp a b d \<cdot> (Comp b c d \<otimes> Hom a b)) x =
                      RTS.Map (Comp a b d) (RTS.Map (Comp b c d \<otimes> Hom a b) x)"
                  using a b c d RTS.Map_comp by fastforce
                also have "... = RTS.Map (Comp a b d)
                                   (RTS.Pack (Hom b d) (Hom a b)
                                     (CbcdXIab.map
                                        (RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x)))"
                  using RTS.Map_prod a b c d by auto
                also have "... = (\<lambda>x. fst x \<star> snd x)
                                   (CbcdXIab.map
                                      (RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x))"
                  using a b d x CbcdXIab.preserves_reflects_arr
                        PU_cdxbc_X_ab.G.preserves_reflects_arr
                        Map_Comp_Pack
                           [of a b d "CbcdXIab.map
                                        (RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x)"]
                  by blast
                also have "... = (\<lambda>x. fst x \<star> snd x)
                                   (RTS.Map (Comp b c d)
                                      (fst
                                        (RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x)),
                                    snd (RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x))"
                  using a b x RTS.Map_ide cdxbc_X_ab.arr_char
                        CbcdXIab.map_simp
                          [of "fst (RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x)"
                              "snd (RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x)"]
                        PU_cdxbc_X_ab.G.preserves_reflects_arr [of x]
                  by auto
                also have "... = (\<lambda>x. fst x \<star> snd x)
                                   (RTS.Map (Comp b c d)
                                      (I (RTS.Rts (RTS.dom (Hom c d \<otimes> Hom b c)))
                                            (fst
                                               (RTS.Unpack
                                                  (Hom c d \<otimes> Hom b c) (Hom a b) x))),
                                    snd (RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x))"
                  using x cdxbc_X_ab.arr_char comp_apply
                        PU_cdxbc_X_ab.G.preserves_reflects_arr [of x]
                  by simp
                also have "... = (\<lambda>x. fst x \<star> snd x)
                                   (RTS.Map (Comp b c d)
                                      ((RTS.Pack (Hom c d) (Hom b c) \<circ>
                                          RTS.Unpack (Hom c d) (Hom b c))
                                            (fst
                                               (RTS.Unpack
                                                  (Hom c d \<otimes> Hom b c) (Hom a b) x))),
                                    snd (RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x))"
                  using PU_cdXbc.inv' by simp
                also have "... = (\<lambda>x. fst x \<star> snd x)
                                   (RTS.Map (Comp b c d)
                                      (RTS.Pack (Hom c d) (Hom b c)
                                         (RTS.Unpack (Hom c d) (Hom b c)
                                            (fst
                                               (RTS.Unpack
                                                  (Hom c d \<otimes> Hom b c) (Hom a b) x)))),
                                    snd (RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x))"
                  by auto
                also have "... = (\<lambda>x. (fst (fst x) \<star> snd (fst x)) \<star> snd x)
                                   ((\<lambda>y. (RTS.Unpack (Hom c d) (Hom b c) (fst y),
                                          snd y))
                                      (RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x))"
                  using b c d x PU_cdxbc_X_ab.G.preserves_reflects_arr [of x]
                        cdxbc_X_ab.arr_char
                          [of "RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x"]
                        Map_Comp_Pack
                          [of b c d
                              "RTS.Unpack (Hom c d) (Hom b c)
                                 (fst (RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x))"]
                  by fastforce
                finally have LHS: "RTS.Map
                                     (Comp a b d \<cdot> (Comp b c d \<otimes> Hom a b)) x =
                                   (\<lambda>x. (fst (fst x) \<star> snd (fst x)) \<star> snd x)
                                     ((\<lambda>y. (RTS.Unpack (Hom c d) (Hom b c) (fst y),
                                            snd y))
                                        (RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x))"
                  by blast

                have "RTS.Map (Comp a c d \<cdot> (Hom c d \<otimes> Comp a b c) \<cdot>
                        \<a>[Hom c d, Hom b c, Hom a b]) x =
                      RTS.Map (Comp a c d)
                        (RTS.Map (Hom c d \<otimes> Comp a b c)
                           (RTS.Map \<a>[Hom c d, Hom b c, Hom a b] x))"
                  using a b c d RTS.Map_comp by fastforce
                also have "... = RTS.Map (Comp a c d)
                                   (RTS.Map (Hom c d \<otimes> Comp a b c)
                                     (RTS.Pack (Hom c d) (Hom b c \<otimes> Hom a b)
                                        (product_simulation.map
                                           (RTS.Rts (Hom c d)) bcXab.resid
                                           (I (RTS.Rts (Hom c d)))
                                           (RTS.Pack (Hom b c) (Hom a b))
                                           (ASSOC.map (RTS.Rts (Hom c d))
                                                      (RTS.Rts (Hom b c))
                                                      (RTS.Rts (Hom a b))
                                              ((product_simulation.map
                                                  (RTS.Rts (Hom c d \<otimes> Hom b c))
                                                  (RTS.Rts (Hom a b))
                                                  (RTS.Unpack (Hom c d) (Hom b c))
                                                  (I (RTS.Rts (Hom a b)))
                                                  (RTS.Unpack
                                                     (Hom c d \<otimes> Hom b c)
                                                     (Hom a b) x)))))))"
                  using a b c d RTS.tensor_agreement RTS.Map_assoc
                  by (auto simp add: RTS.comp_arr_ide)
                also have "... = RTS.Map (Comp a c d)
                                   (RTS.Map (Hom c d \<otimes> Comp a b c)
                                     (RTS.Pack (Hom c d) (Hom b c \<otimes> Hom a b)
                                        (product_simulation.map
                                           (RTS.Rts (Hom c d)) bcXab.resid
                                           (I (RTS.Rts (Hom c d)))
                                           (RTS.Pack (Hom b c) (Hom a b))
                                           (ASSOC.map (RTS.Rts (Hom c d))
                                                      (RTS.Rts (Hom b c))
                                                      (RTS.Rts (Hom a b))
                                              (((\<lambda>x. (RTS.Unpack
                                                        (Hom c d) (Hom b c) (fst x),
                                                      RTS.Map (Hom a b) (snd x)))
                                                  (RTS.Unpack
                                                     (Hom c d \<otimes> Hom b c)
                                                     (Hom a b) x)))))))"
                  using a b c d x RTS.Map_ide
                        PU_cdxbc_X_ab.G.preserves_reflects_arr [of x]
                        cdxbc_X_ab.arr_char
                        Ucdxbc_X_Iab.map_simp
                          [of "fst (RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x)"
                              "snd (RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x)"]
                  by simp
                also have "... = RTS.Map (Comp a c d)
                                   (RTS.Map (Hom c d \<otimes> Comp a b c)
                                     (RTS.Pack (Hom c d) (Hom b c \<otimes> Hom a b)
                                        (product_simulation.map
                                           (RTS.Rts (Hom c d)) bcXab.resid
                                           (I (RTS.Rts (Hom c d)))
                                           (RTS.Pack (Hom b c) (Hom a b))
                                           (fst (RTS.Unpack (Hom c d) (Hom b c)
                                              (fst
                                                 (RTS.Unpack
                                                    (Hom c d \<otimes> Hom b c) (Hom a b) x))),
                                            snd (RTS.Unpack (Hom c d) (Hom b c)
                                              (fst
                                                 (RTS.Unpack
                                                    (Hom c d \<otimes> Hom b c) (Hom a b) x))),
                                            snd
                                              (RTS.Unpack
                                                 (Hom c d \<otimes> Hom b c) (Hom a b) x)))))"
                proof -
                  interpret A: ASSOC \<open>RTS.Rts (Hom c d)\<close> \<open>RTS.Rts (Hom b c)\<close>
                                 \<open>RTS.Rts (Hom a b)\<close>
                    ..
                  show ?thesis
                    using a b c d x cdxbc_X_ab.arr_char cdXbc.arr_char
                          PU_cdxbc_X_ab.G.preserves_reflects_arr
                          PU_cdXbc.G.preserves_reflects_arr
                          A.map_eq RTS.Map_ide
                    by auto
                qed
                also have "... = RTS.Map (Comp a c d)
                                   (RTS.Map (Hom c d \<otimes> Comp a b c)
                                     (RTS.Pack (Hom c d) (Hom b c \<otimes> Hom a b)
                                       (fst ?x,
                                        RTS.Pack (Hom b c) (Hom a b)
                                          (snd ?x, snd ?w))))"
                   using c d x RTS.Map_ide Icd_X_Pbcxab.map_simp
                         cdxbc_X_ab.arr_char
                         PU_cdxbc_X_ab.G.preserves_reflects_arr [of x]
                         PU_cdXbc.G.preserves_reflects_arr
                           [of "fst (RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x)"]
                   by auto
                also have "... = RTS.Map (Comp a c d)
                                   (RTS.Pack (Hom c d) (Hom a c)
                                      (IcdXCabc.map
                                         ((RTS.Unpack
                                             (Hom c d) (Hom b c \<otimes> Hom a b) \<circ>
                                                RTS.Pack (Hom c d) (Hom b c \<otimes> Hom a b))
                                            (fst ?x,
                                             RTS.Pack (Hom b c) (Hom a b)
                                               (snd ?x, snd ?w)))))"
                  using a b c d x RTS.Map_prod by auto
                also have "... = RTS.Map (Comp a c d)
                                   (RTS.Pack (Hom c d) (Hom a c)
                                      (IcdXCabc.map
                                         (fst ?x,
                                          RTS.Pack (Hom b c) (Hom a b)
                                            (snd ?x, snd ?w))))"
                proof - 
                  have "cd_X_bcxab.arr
                          (fst ?x, RTS.Pack (Hom b c) (Hom a b) (snd ?x, snd ?w))"
                    using fst_x snd_x snd_w PU_bcXab.F.preserves_reflects_arr
                    by fastforce
                  thus ?thesis
                    using PU_cd_X_bcxab.inv by auto
                qed
                also have "... = RTS.Map (Comp a c d)
                                   (RTS.Pack (Hom c d) (Hom a c)
                                     (RTS.Map (Hom c d) (fst ?x),
                                      RTS.Map (Comp a b c)
                                        (RTS.Pack (Hom b c) (Hom a b)
                                           (snd ?x, snd ?w))))"
                  using a b c d x fst_x snd_x snd_w
                        IcdXCabc.map_simp
                          [of "fst ?x"
                              "RTS.Pack (Hom b c) (Hom a b) (snd ?x, snd ?w)"]
                  by fastforce
                also have "... = fst ?x \<star> (snd ?x \<star> snd ?w)"
                proof -
                  have "ac.arr (snd ?x \<star> snd ?w)"
                    using a b c snd_w snd_x HOM_arr_char arr_coincidence
                    by auto
                  thus ?thesis
                    using a b c d fst_x RTS.Map_ide snd_x snd_w Map_Comp_Pack
                    by auto
                qed
                also have "... = (\<lambda>x. (fst (fst x) \<star> snd (fst x)) \<star> snd x)
                                   ((\<lambda>y. (RTS.Unpack (Hom c d) (Hom b c) (fst y),
                                          snd y))
                                      (RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x))"
                  using H.comp_assoc by simp
                finally have RHS: "RTS.Map
                                     (Comp a c d \<cdot> (Hom c d \<otimes> Comp a b c) \<cdot>
                                        \<a>[Hom c d, Hom b c, Hom a b]) x =
                                   (\<lambda>x. (fst (fst x) \<star> snd (fst x)) \<star> snd x)
                                      ((\<lambda>y. (RTS.Unpack (Hom c d) (Hom b c) (fst y),
                                             snd y))
                                         (RTS.Unpack (Hom c d \<otimes> Hom b c) (Hom a b) x))"
                  by blast
                show ?thesis using LHS RHS by auto
              qed
            qed
          qed
        qed
      qed
    qed

    proposition is_rts_enriched_category:
    shows "rts_enriched_category Obj Hom Id Comp"
      ..

    lemma HOM_agreement:
    assumes "H.ide a" and "H.ide b"
    shows "HOM\<^sub>E\<^sub>C a b = HOM a b"
      using assms Hom_def RTS.bij_mkide(3) by auto

  end

subsection "Functoriality"

  text\<open>
    If we are to construct an enriched functor from a given RTS-functor \<open>F\<close>, then we need
    a base category \<open>\<^bold>R\<^bold>T\<^bold>S\<close> that is large enough to provide objects for all the required
    hom-RTS's.  So the arrow type of this category will need to embed the arrow types
    of both the domain \<open>A\<close> and the codomain \<open>B\<close> RTS of the given RTS-functor \<open>F\<close>.
    Here I have assumed that both of these arrow types are in fact the same type \<open>'A\<close>
    and in addition that \<open>'A\<close> is a universe, so that it supports the construction of the
    cartesian closed base category \<open>\<^bold>R\<^bold>T\<^bold>S\<close>.  At the cost of having to deal with coercions,
    we could more generally just assume injections from the arrow types of \<open>A\<close>
    and \<open>B\<close> into a common universe \<open>'C\<close>, but we haven't bothered to do that.
  \<close>

  locale enriched_functor_of_rts_functor =
    universe arr_type +
    RTS: rtscat arr_type +
    A: locally_small_rts_category resid\<^sub>A comp\<^sub>A +
    B: locally_small_rts_category resid\<^sub>B comp\<^sub>B +
    F: rts_functor resid\<^sub>A comp\<^sub>A resid\<^sub>B comp\<^sub>B F
  for arr_type :: "'A itself"
  and resid\<^sub>A :: "'A resid"  (infix \<open>\\<^sub>A\<close> 70)
  and comp\<^sub>A :: "'A comp"    (infixr \<open>\<star>\<^sub>A\<close> 53)
  and resid\<^sub>B :: "'A resid"  (infix \<open>\\<^sub>B\<close> 70)
  and comp\<^sub>B :: "'A comp"    (infixr \<open>\<star>\<^sub>B\<close> 53)
  and F :: "'A \<Rightarrow> 'A"
  begin

    interpretation A: enriched_category_of_rts_category arr_type resid\<^sub>A comp\<^sub>A ..
    interpretation B: enriched_category_of_rts_category arr_type resid\<^sub>B comp\<^sub>B ..

    (*
     * TODO: I haven't assumed that the object map of an enriched functor is extensional.
     * Perhaps I should have.
     *)

    definition F\<^sub>o
    where "F\<^sub>o a \<equiv> if A.H.ide a then F a else B.null"

    definition F\<^sub>a
    where "F\<^sub>a a b \<equiv> if A.H.ide a \<and> A.H.ide b
                    then RTS.mkarr (A.HOM\<^sub>E\<^sub>C a b) (B.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b))
                           (\<lambda>t. if residuation.arr (A.HOM\<^sub>E\<^sub>C a b) t
                                then F t
                                else ResiduatedTransitionSystem.partial_magma.null
                                       (B.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)))
                    else RTS.null"

    lemma sub_rts_resid_eq:
    assumes "a \<in> A.Obj" and "b \<in> A.Obj"
    shows "sub_rts.resid resid\<^sub>A (\<lambda>t. A.H.in_hom t a b) = A.HOM\<^sub>E\<^sub>C a b"
    and "sub_rts.resid resid\<^sub>B (\<lambda>t. B.H.in_hom t (F\<^sub>o a) (F\<^sub>o b)) =
         B.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)"
    proof -
      have 1: "\<And>a. a \<in> Collect A.H.ide \<Longrightarrow> F\<^sub>o a \<in> Collect B.H.ide"
        unfolding F\<^sub>o_def by simp
      interpret DOM: sub_rts resid\<^sub>A \<open>\<lambda>t. A.H.in_hom t a b\<close>
        using assms A.sub_rts_HOM by metis
      interpret COD: sub_rts resid\<^sub>B \<open>\<lambda>t. B.H.in_hom t (F\<^sub>o a) (F\<^sub>o b)\<close>
        using assms 1 B.sub_rts_HOM by metis
      show "DOM.resid = A.HOM\<^sub>E\<^sub>C a b"
        using assms DOM.resid_def A.Hom_def RTS.bij_mkide(3) by simp
      show "COD.resid = B.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)"
        using assms 1 B.Hom_def COD.resid_def RTS.bij_mkide(3) by auto
    qed

    sublocale rts_enriched_functor
                \<open>Collect A.H.ide\<close> A.Hom A.Id A.Comp
                \<open>Collect B.H.ide\<close> B.Hom B.Id B.Comp
                F\<^sub>o F\<^sub>a
    proof
      show 1: "\<And>a. a \<in> Collect A.H.ide \<Longrightarrow> F\<^sub>o a \<in> Collect B.H.ide"
        unfolding F\<^sub>o_def by simp
      show "\<And>a b. a \<notin> Collect A.H.ide \<or> b \<notin> Collect A.H.ide \<Longrightarrow> F\<^sub>a a b = RTS.null"
        unfolding F\<^sub>a_def by auto
      show 2: "\<And>a b. \<lbrakk>a \<in> Collect A.H.ide; b \<in> Collect A.H.ide\<rbrakk> \<Longrightarrow>
                        \<guillemotleft>F\<^sub>a a b : A.Hom a b \<rightarrow> B.Hom (F\<^sub>o a) (F\<^sub>o b)\<guillemotright>"
      proof -
        fix a b
        assume a: "a \<in> Collect A.H.ide" and b: "b \<in> Collect A.H.ide"
        interpret DOM: sub_rts resid\<^sub>A \<open>\<lambda>t. A.H.in_hom t a b\<close>
          using a b A.sub_rts_HOM by metis
        interpret COD: sub_rts resid\<^sub>B \<open>\<lambda>t. B.H.in_hom t (F\<^sub>o a) (F\<^sub>o b)\<close>
          using a b 1 B.sub_rts_HOM by metis
        interpret F\<^sub>a_ab: simulation DOM.resid COD.resid
                           \<open>\<lambda>t. if DOM.arr t then F t else COD.null\<close>
        proof
          show "\<And>t. \<not> DOM.arr t \<Longrightarrow>
                         (if DOM.arr t then F t else COD.null) = COD.null"
            by simp
          show "\<And>t u. DOM.con t u \<Longrightarrow>
                         COD.con (if DOM.arr t then F t else COD.null)
                                 (if DOM.arr u then F u else COD.null)"
            using COD.con_char DOM.arr_char DOM.con_char F\<^sub>o_def a b by auto
          show "\<And>t u. DOM.con t u \<Longrightarrow>
                         (if DOM.arr (DOM.resid t u) then F (DOM.resid t u)
                          else COD.null) =
                         COD.resid (if DOM.arr t then F t else COD.null)
                                   (if DOM.arr u then F u else COD.null)"
            using a b 1 F\<^sub>o_def COD.con_char DOM.arr_char DOM.con_char
                  DOM.resid_def COD.resid_def DOM.resid_closed
            by auto
        qed
        show "\<guillemotleft>F\<^sub>a a b : A.Hom a b \<rightarrow> B.Hom (F\<^sub>o a) (F\<^sub>o b)\<guillemotright>"
        proof
          have 2: "residuation.arr (A.HOM\<^sub>E\<^sub>C a b) = DOM.arr"
            using a b DOM.arr_char A.Hom_def RTS.bij_mkide(3) by simp
          have 3: "ResiduatedTransitionSystem.partial_magma.null
                     (B.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)) =
                   COD.null"
            using a b 1 COD.null_char B.Hom_def RTS.bij_mkide(3) by auto
          show 4: "RTS.arr (F\<^sub>a a b)"
          proof (intro RTS.arrI\<^sub>R\<^sub>T\<^sub>S\<^sub>C)
            show "extensional_rts DOM.resid \<and> small_rts DOM.resid"
              using a b A.V.extensional_rts_axioms DOM.preserves_extensional_rts
                    sub_rts_resid_eq
              by auto
            show "extensional_rts COD.resid \<and> small_rts COD.resid"
              using a b 1 B.V.extensional_rts_axioms COD.preserves_extensional_rts
                    sub_rts_resid_eq(2)
              by auto
            have "(\<lambda>t. if DOM.arr t then F t
                       else ResiduatedTransitionSystem.partial_magma.null
                              (B.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b))) =
                  (\<lambda>t. if DOM.arr t then F t else COD.null)"
              using a b 3 sub_rts_resid_eq F\<^sub>a_def RTS.Map_mkarr
              by auto
            thus "F\<^sub>a a b \<in> RTS.mkarr DOM.resid COD.resid `
                             Collect (simulation DOM.resid COD.resid)"
              unfolding F\<^sub>a_def
              using a b 1 3 sub_rts_resid_eq F\<^sub>a_ab.simulation_axioms
                    RTS.Map_mkarr
              by auto
          qed
          show "RTS.dom (F\<^sub>a a b) = A.Hom a b"
            using 4 F\<^sub>a_def by fastforce
          show "RTS.cod (F\<^sub>a a b) = B.Hom (F\<^sub>o a) (F\<^sub>o b)"
            using 4 F\<^sub>o_def F\<^sub>a_def by fastforce
        qed
      qed
      show "\<And>a. a \<in> Collect A.H.ide \<Longrightarrow> F\<^sub>a a a \<cdot> A.Id a = B.Id (F\<^sub>o a)"
      proof -
        fix a
        assume a: "a \<in> Collect A.H.ide"
        interpret HOM\<^sub>A: sub_rts resid\<^sub>A \<open>\<lambda>t. A.H.in_hom t a a\<close>
          using a A.sub_rts_HOM by metis
        interpret HOM\<^sub>B: sub_rts resid\<^sub>B \<open>\<lambda>t. B.H.in_hom t (F\<^sub>o a) (F\<^sub>o a)\<close>
          using a 1 B.sub_rts_HOM by metis
        have 3: "RTS.arr (F\<^sub>a a a \<cdot> A.Id a)"
          using a 2 A.arr_coincidence A.Id_in_hom by auto
        have 4: "F\<^sub>a a a \<cdot> A.Id a =
                 RTS.mkarr (A.HOM\<^sub>E\<^sub>C a a) (B.HOM\<^sub>E\<^sub>C (F a) (F a))
                   (\<lambda>t. if HOM\<^sub>A.arr t then F t else HOM\<^sub>B.null) \<cdot>
                 RTS.mkarr RTS.One.resid (A.HOM\<^sub>E\<^sub>C a a)
                   (\<lambda>t. if RTS.One.arr t then a else HOM\<^sub>A.null)"
        proof -
          have "A.HOM\<^sub>E\<^sub>C a a = HOM\<^sub>A.resid"
            using a HOM\<^sub>A.resid_def A.Hom_def RTS.bij_mkide(3) by simp
          moreover have "B.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o a) = HOM\<^sub>B.resid"
            using a 1 HOM\<^sub>B.resid_def B.Hom_def [of "F\<^sub>o a" "F\<^sub>o a"] RTS.bij_mkide(3)
            by simp
          ultimately show ?thesis
            unfolding F\<^sub>o_def F\<^sub>a_def A.Id_def B.Id_def
            using a A.arr_coincidence A.Hom_def B.Hom_def
            apply auto[1]
            using F\<^sub>o_def \<open>B.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o a) = HOM\<^sub>B.resid\<close> by presburger
        qed
        also have "... = RTS.mkarr RTS.One.resid (B.HOM\<^sub>E\<^sub>C (F a) (F a))
                           ((\<lambda>t. if HOM\<^sub>A.arr t then F t else HOM\<^sub>B.null) \<circ>
                              (\<lambda>t. if RTS.One.arr t then a else HOM\<^sub>A.null))"
          using a 1 3 4 RTS.comp_mkarr by auto
        also have "... = RTS.mkarr RTS.One.resid (B.HOM\<^sub>E\<^sub>C (F a) (F a))
                           (\<lambda>t. if RTS.One.arr t then F a else HOM\<^sub>B.null)"
          (is "?LHS = ?RHS")
        proof (intro RTS.arr_eqI)
          interpret HOM_Fa_Fa: hom_rts arr_type B.Obj B.Hom B.Id B.Comp
                                 \<open>F a\<close> \<open>F a\<close>
            using a by unfold_locales auto
          have 5: "simulation RTS.One.resid (B.HOM\<^sub>E\<^sub>C (F a) (F a))
                     (\<lambda>t. if RTS.One.arr t then F a else HOM\<^sub>B.null)"
          proof -
            have "(\<lambda>t. if RTS.One.arr t then F a
                       else ResiduatedTransitionSystem.partial_magma.null
                              (B.HOM (F a) (F a))) =
                  (\<lambda>t. if RTS.One.arr t then F a else HOM\<^sub>B.null)"
              using F\<^sub>o_def a by fastforce
            thus ?thesis
              using a RTS.bij_mkide(3) B.Id_in_hom [of "F a"]
                    RTS.arrD(3) [of "B.Id (F a)"]
                    B.Id_def RTS.Map_mkarr
              by auto
          qed
          have 6: "extensional_rts (B.HOM\<^sub>E\<^sub>C (F a) (F a))"
            using a by force
          have 7: "small_rts (B.HOM\<^sub>E\<^sub>C (F a) (F a))"
            using a by force
          have 8: "RTS.arr ?LHS"
            using 3 calculation by auto
          have 9: "RTS.arr ?RHS"
            using 5 6 7 RTS.One.extensional_rts_axioms
                  RTS.One.small_rts_axioms
            by auto
          show "RTS.par ?LHS ?RHS"
            using 8 9 by auto
          show "RTS.Map ?LHS = RTS.Map ?RHS"
          proof
            fix x
            show "RTS.Map ?LHS x = RTS.Map ?RHS x"
              using a 8 9 RTS.Map_mkarr HOM\<^sub>A.arr_char HOM\<^sub>A.null_char
                    A.H.ide_in_hom
              by auto
          qed
        qed
        also have "... = B.Id (F\<^sub>o a)"
          unfolding F\<^sub>o_def B.Id_def
          using a by auto
        finally show "F\<^sub>a a a \<cdot> A.Id a = B.Id (F\<^sub>o a)" by blast
      qed
      show "\<And>a b c. \<lbrakk>a \<in> A.Obj; b \<in> A.Obj; c \<in> A.Obj\<rbrakk>
                       \<Longrightarrow> B.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b) =
                           F\<^sub>a a c \<cdot> A.Comp a b c"
      proof -
        fix a b c
        assume a: "a \<in> Collect A.H.ide" and b: "b \<in> Collect A.H.ide"
        and c: "c \<in> Collect A.H.ide"
        interpret HOM\<^sub>A_ab: sub_rts resid\<^sub>A \<open>\<lambda>t. A.H.in_hom t a b\<close>
          using a b A.sub_rts_HOM by metis
        interpret HOM\<^sub>A_ac: sub_rts resid\<^sub>A \<open>\<lambda>t. A.H.in_hom t a c\<close>
          using a c A.sub_rts_HOM by metis
        interpret HOM\<^sub>A_bc: sub_rts resid\<^sub>A \<open>\<lambda>t. A.H.in_hom t b c\<close>
          using b c A.sub_rts_HOM by metis
        interpret HOM\<^sub>B_ab: sub_rts resid\<^sub>B \<open>\<lambda>t. B.H.in_hom t (F\<^sub>o a) (F\<^sub>o b)\<close>
          using a b 1 B.sub_rts_HOM by metis
        interpret HOM\<^sub>B_ac: sub_rts resid\<^sub>B \<open>\<lambda>t. B.H.in_hom t (F\<^sub>o a) (F\<^sub>o c)\<close>
          using a c 1 B.sub_rts_HOM by metis
        interpret HOM\<^sub>B_bc: sub_rts resid\<^sub>B \<open>\<lambda>t. B.H.in_hom t (F\<^sub>o b) (F\<^sub>o c)\<close>
          using b c 1 B.sub_rts_HOM by metis
        interpret F\<^sub>a_bc: simulation HOM\<^sub>A_bc.resid HOM\<^sub>B_bc.resid
                           \<open>RTS.Map (F\<^sub>a b c)\<close>
          using b c 1 2 [of b c] A.Hom_def B.Hom_def RTS.bij_mkide(3)
                RTS.arrD(3) [of "F\<^sub>a b c"]
          by auto
        interpret F\<^sub>a_ab: simulation HOM\<^sub>A_ab.resid HOM\<^sub>B_ab.resid
                           \<open>RTS.Map (F\<^sub>a a b)\<close>
          using a b 1 2 [of a b] A.Hom_def B.Hom_def RTS.bij_mkide(3)
                RTS.arrD(3) [of "F\<^sub>a a b"]
          by auto
        interpret F\<^sub>a_bc_x_F\<^sub>a_ab: product_simulation
                                   HOM\<^sub>A_bc.resid HOM\<^sub>A_ab.resid
                                   HOM\<^sub>B_bc.resid HOM\<^sub>B_ab.resid
                                   \<open>RTS.Map (F\<^sub>a b c)\<close> \<open>RTS.Map (F\<^sub>a a b)\<close>
          ..

        interpret HOM_bc: extensional_rts \<open>A.HOM\<^sub>E\<^sub>C b c\<close>
          using b c by simp
        interpret HOM_ab: extensional_rts \<open>A.HOM\<^sub>E\<^sub>C a b\<close>
          using a b by simp
        interpret HOM_ac: extensional_rts \<open>A.HOM\<^sub>E\<^sub>C a c\<close>
          using a c by simp
        interpret HOM_bc_x_HOM_ab: product_rts
                                     \<open>A.HOM\<^sub>E\<^sub>C b c\<close> \<open>A.HOM\<^sub>E\<^sub>C a b\<close>
          ..
        interpret B_HOM_bc: extensional_rts \<open>B.HOM\<^sub>E\<^sub>C (F\<^sub>o b) (F\<^sub>o c)\<close>
          using b c 1 by simp
        interpret B_HOM_ab: extensional_rts \<open>B.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)\<close>
          using a b 1 by simp
        interpret B_HOM_bc_x_B_HOM_ab: product_rts
                                         \<open>B.HOM\<^sub>E\<^sub>C (F\<^sub>o b) (F\<^sub>o c)\<close>
                                         \<open>B.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)\<close>
          ..
        interpret U: simulation
                       \<open>RTS.Rts (A.Hom b c \<otimes> A.Hom a b)\<close>
                       \<open>HOM_bc_x_HOM_ab.resid\<close>
                       \<open>RTS.Unpack (A.Hom b c) (A.Hom a b)\<close>
          using a b c RTS.simulation_Unpack by simp

        show "B.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b) =
              F\<^sub>a a c \<cdot> A.Comp a b c"
        proof (intro RTS.arr_eqI)
          show 3: "RTS.par
                     (B.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b))
                     (F\<^sub>a a c \<cdot> A.Comp a b c)"
          proof (intro conjI)
            show "RTS.seq (B.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c)) (F\<^sub>a b c \<otimes> F\<^sub>a a b)"
              using a b c 1 2 [of b c] 2 [of a b]
                    RTS.prod_simps [of "F\<^sub>a b c" "F\<^sub>a a b"]
              apply (intro RTS.seqI)
                apply auto[1]
              by fastforce+
            show "RTS.seq (F\<^sub>a a c) (A.Comp a b c)"
              using a b c 1 2 A.Comp_in_hom by blast
            show "RTS.dom (B.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b)) =
                  RTS.dom (F\<^sub>a a c \<cdot> A.Comp a b c)"
              using a b c 1 2 [of b c] 2 [of a b] 2 [of a c] by fastforce
            show "RTS.cod (B.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b)) =
                  RTS.cod (F\<^sub>a a c \<cdot> A.Comp a b c)"
              using a b c 1 2 [of b c] 2 [of a b] 2 [of a c] by fastforce
          qed
          show "RTS.Map (B.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b)) =
                RTS.Map (F\<^sub>a a c \<cdot> A.Comp a b c)"
          proof -
            have "RTS.Map (B.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b)) =
                  RTS.Map (B.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c)) \<circ>
                             RTS.Map (F\<^sub>a b c \<otimes> F\<^sub>a a b)"
              using a b c 1 2 [of b c] 2 [of a b] 2 [of a c] 3 RTS.Map_comp
              by auto
            also have "... = (\<lambda>t. fst
                                    (RTS.Unpack
                                       (B.Hom (F\<^sub>o b) (F\<^sub>o c))
                                       (B.Hom (F\<^sub>o a) (F\<^sub>o b)) t) \<star>\<^sub>B
                                    snd
                                      (RTS.Unpack
                                         (B.Hom (F\<^sub>o b) (F\<^sub>o c))
                                         (B.Hom (F\<^sub>o a) (F\<^sub>o b)) t)) \<circ>
                               (RTS.Pack (RTS.cod (F\<^sub>a b c)) (RTS.cod (F\<^sub>a a b)) \<circ>
                                  F\<^sub>a_bc_x_F\<^sub>a_ab.map \<circ>
                                    RTS.Unpack
                                      (RTS.dom (F\<^sub>a b c)) (RTS.dom (F\<^sub>a a b)))"
            proof -
              have "RTS.Map (B.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c)) =
                    (\<lambda>t. fst (RTS.Unpack
                                (B.Hom (F\<^sub>o b) (F\<^sub>o c)) (B.Hom (F\<^sub>o a) (F\<^sub>o b)) t) \<star>\<^sub>B
                         snd (RTS.Unpack
                                (B.Hom (F\<^sub>o b) (F\<^sub>o c)) (B.Hom (F\<^sub>o a) (F\<^sub>o b)) t))"
                using a b c 1 2 B.Comp_def RTS.Map_mkarr
                      B.Comp_in_hom [of "F\<^sub>o a" "F\<^sub>o b" "F\<^sub>o c"]
                by auto
              moreover have "RTS.Map (F\<^sub>a b c \<otimes> F\<^sub>a a b) =
                             RTS.Pack (RTS.cod (F\<^sub>a b c)) (RTS.cod (F\<^sub>a a b)) \<circ>
                               F\<^sub>a_bc_x_F\<^sub>a_ab.map \<circ>
                                 RTS.Unpack (RTS.dom (F\<^sub>a b c)) (RTS.dom (F\<^sub>a a b))"
              proof -
                have "RTS.Rts (RTS.dom (F\<^sub>a b c)) = HOM\<^sub>A_bc.resid"
                  using b c 2 [of b c] sub_rts_resid_eq by auto
                moreover have "RTS.Rts (RTS.dom (F\<^sub>a a b)) = HOM\<^sub>A_ab.resid"
                  using a b 2 [of a b] sub_rts_resid_eq by auto
                ultimately have "product_simulation.map
                        (RTS.Rts (RTS.dom (F\<^sub>a b c))) (RTS.Rts (RTS.dom (F\<^sub>a a b)))
                        (RTS.Map (F\<^sub>a b c)) (RTS.Map (F\<^sub>a a b)) =
                      F\<^sub>a_bc_x_F\<^sub>a_ab.map"
                  using a b c 1 2 [of b c] 2 [of a b] F\<^sub>a_def RTS.dom_mkarr by auto
                thus ?thesis
                  using a b c 1 2 [of b c] 2 [of a b] A.Hom_def B.Hom_def
                        RTS.in_homE RTS.Map_prod [of "F\<^sub>a b c" "F\<^sub>a a b"]
                  by auto
              qed
              ultimately show ?thesis by force
            qed
            also have "... = (\<lambda>t. fst
                                    (RTS.Unpack
                                       (B.Hom (F\<^sub>o b) (F\<^sub>o c)) (B.Hom (F\<^sub>o a) (F\<^sub>o b))
                                         (RTS.Pack
                                            (B.Hom (F\<^sub>o b) (F\<^sub>o c))
                                            (B.Hom (F\<^sub>o a) (F\<^sub>o b))
                                             (F\<^sub>a_bc_x_F\<^sub>a_ab.map
                                                (RTS.Unpack
                                                   (A.Hom b c) (A.Hom a b) t)))) \<star>\<^sub>B
                                    snd
                                      (RTS.Unpack
                                         (B.Hom (F\<^sub>o b) (F\<^sub>o c)) (B.Hom (F\<^sub>o a) (F\<^sub>o b))
                                          (RTS.Pack
                                             (B.Hom (F\<^sub>o b) (F\<^sub>o c))
                                             (B.Hom (F\<^sub>o a) (F\<^sub>o b))
                                             (F\<^sub>a_bc_x_F\<^sub>a_ab.map
                                                (RTS.Unpack
                                                   (A.Hom b c) (A.Hom a b) t)))))"
              using a b c 2 [of a b] 2 [of b c] by fastforce
            also have "... = (\<lambda>t. fst (F\<^sub>a_bc_x_F\<^sub>a_ab.map
                                         (RTS.Unpack (A.Hom b c) (A.Hom a b) t)) \<star>\<^sub>B
                                  snd (F\<^sub>a_bc_x_F\<^sub>a_ab.map
                                         (RTS.Unpack (A.Hom b c) (A.Hom a b) t)))"
            proof
              fix t
              interpret PU: inverse_simulations
                              \<open>RTS.Rts
                                 (RTS.dom
                                    (B.Hom (F\<^sub>o b) (F\<^sub>o c) \<otimes> B.Hom (F\<^sub>o a) (F\<^sub>o b)))\<close>
                              \<open>product_rts.resid
                                 (B.HOM\<^sub>E\<^sub>C (F\<^sub>o b) (F\<^sub>o c)) (B.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b))\<close>
                              \<open>RTS.Pack
                                 (B.Hom (F\<^sub>o b) (F\<^sub>o c)) (B.Hom (F\<^sub>o a) (F\<^sub>o b))\<close>
                              \<open>RTS.Unpack
                                  (B.Hom (F\<^sub>o b) (F\<^sub>o c)) (B.Hom (F\<^sub>o a) (F\<^sub>o b))\<close>
                using a b c 1 RTS.inverse_simulations_Pack_Unpack by simp
              show "fst
                      (RTS.Unpack
                         (B.Hom (F\<^sub>o b) (F\<^sub>o c)) (B.Hom (F\<^sub>o a) (F\<^sub>o b))
                         (RTS.Pack (B.Hom (F\<^sub>o b) (F\<^sub>o c)) (B.Hom (F\<^sub>o a) (F\<^sub>o b))
                            (F\<^sub>a_bc_x_F\<^sub>a_ab.map
                               (RTS.Unpack (A.Hom b c) (A.Hom a b) t)))) \<star>\<^sub>B
                             snd (RTS.Unpack
                                    (B.Hom (F\<^sub>o b) (F\<^sub>o c)) (B.Hom (F\<^sub>o a) (F\<^sub>o b))
                                    (RTS.Pack
                                       (B.Hom (F\<^sub>o b) (F\<^sub>o c)) (B.Hom (F\<^sub>o a) (F\<^sub>o b))
                                       (F\<^sub>a_bc_x_F\<^sub>a_ab.map
                                          (RTS.Unpack (A.Hom b c) (A.Hom a b) t)))) =
                   fst
                     (F\<^sub>a_bc_x_F\<^sub>a_ab.map (RTS.Unpack (A.Hom b c) (A.Hom a b) t)) \<star>\<^sub>B
                   snd
                     (F\<^sub>a_bc_x_F\<^sub>a_ab.map (RTS.Unpack (A.Hom b c) (A.Hom a b) t))"
              proof (cases "U.A.arr t")
                show "\<not> U.A.arr t \<Longrightarrow> ?thesis"
                  using a b c sub_rts_resid_eq
                        F\<^sub>a_bc_x_F\<^sub>a_ab.extensional PU.F.extensional PU.G.extensional
                        U.extensional F\<^sub>a_bc.extensional F\<^sub>a_ab.extensional
                        PU.A.not_arr_null B_HOM_bc_x_B_HOM_ab.not_arr_null
                  by auto
                assume t: "U.A.arr t"
                show ?thesis
                  using a b c t 1 RTS.Unpack_Pack F\<^sub>a_bc_x_F\<^sub>a_ab.preserves_reflects_arr
                        U.preserves_reflects_arr sub_rts_resid_eq
                  by auto
              qed
            qed
            also have "... =
                       (\<lambda>t. F (fst (RTS.Unpack (A.Hom b c) (A.Hom a b) t)) \<star>\<^sub>B
                            F (snd (RTS.Unpack (A.Hom b c) (A.Hom a b) t)))"
            proof
              fix t
              show "fst
                      (F\<^sub>a_bc_x_F\<^sub>a_ab.map
                         (RTS.Unpack (A.Hom b c) (A.Hom a b) t)) \<star>\<^sub>B
                    snd
                      (F\<^sub>a_bc_x_F\<^sub>a_ab.map
                         (RTS.Unpack (A.Hom b c) (A.Hom a b) t)) =
                    F (fst (RTS.Unpack (A.Hom b c) (A.Hom a b) t)) \<star>\<^sub>B
                    F (snd (RTS.Unpack (A.Hom b c) (A.Hom a b) t))"
              proof (cases "U.A.arr t")
                show "\<not> U.A.arr t \<Longrightarrow> ?thesis"
                  using a b c U.extensional F\<^sub>a_bc_x_F\<^sub>a_ab.extensional F.extensional
                        HOM\<^sub>A_bc.null_char HOM\<^sub>A_ab.null_char HOM\<^sub>B_bc.null_char
                        HOM\<^sub>B_ab.null_char F\<^sub>a_bc.extensional F\<^sub>a_ab.extensional
                        sub_rts_resid_eq HOM\<^sub>A_bc.not_arr_null HOM\<^sub>A_ab.not_arr_null
                  by auto
                assume t: "U.A.arr t"
                show ?thesis
                  using a b c t 1 F\<^sub>a_bc_x_F\<^sub>a_ab.map_def U.preserves_reflects_arr
                        sub_rts_resid_eq B_HOM_ab.extensional_rts_axioms
                        B_HOM_bc.extensional_rts_axioms F\<^sub>a_def
                        HOM_ab.extensional_rts_axioms HOM_bc.extensional_rts_axioms
                        RTS.bij_mkarr(3)
                  by auto
              qed
            qed
            also have "... = (\<lambda>t. F (fst (RTS.Unpack (A.Hom b c) (A.Hom a b) t) \<star>\<^sub>A
                                     snd (RTS.Unpack (A.Hom b c) (A.Hom a b) t)))"
            proof
              fix t
              show "F (fst (RTS.Unpack (A.Hom b c) (A.Hom a b) t)) \<star>\<^sub>B
                    F (snd (RTS.Unpack (A.Hom b c) (A.Hom a b) t)) =
                    F (fst (RTS.Unpack (A.Hom b c) (A.Hom a b) t) \<star>\<^sub>A
                       snd (RTS.Unpack (A.Hom b c) (A.Hom a b) t))"
              proof (cases "U.A.arr t")
                show "\<not> U.A.arr t \<Longrightarrow> ?thesis"
                  using a b c U.extensional F.extensional A.HOM_null_char
                        A.H.extensional B.H.extensional
                        A.H.null_is_zero(2) A.null_coincidence
                        B.H.null_is_zero(2) B.null_coincidence
                  by auto
                assume t: "U.A.arr t"
                have "A.H.seq (fst (RTS.Unpack (A.Hom b c) (A.Hom a b) t)) 
                              (snd (RTS.Unpack (A.Hom b c) (A.Hom a b) t))"
                  using A.HOM_arr_char HOM_bc_x_HOM_ab.arr_char a b c t by blast
                thus ?thesis
                  using a b c t U.preserves_reflects_arr F.preserves_comp
                  by auto
              qed
            qed
            also have "... = (\<lambda>t. if HOM_ac.arr t then F t
                                  else ResiduatedTransitionSystem.partial_magma.null
                                         (B.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o c))) \<circ>
                               (\<lambda>t. fst (RTS.Unpack (A.Hom b c) (A.Hom a b) t) \<star>\<^sub>A
                                    snd (RTS.Unpack (A.Hom b c) (A.Hom a b) t))"
            proof
              fix t
              show "F (fst (RTS.Unpack (A.Hom b c) (A.Hom a b) t) \<star>\<^sub>A
                       snd (RTS.Unpack (A.Hom b c) (A.Hom a b) t)) =
                    ((\<lambda>t. if HOM_ac.arr t
                          then F t
                          else ResiduatedTransitionSystem.partial_magma.null
                                 (B.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o c))) \<circ>
                      (\<lambda>t. fst (RTS.Unpack (A.Hom b c) (A.Hom a b) t) \<star>\<^sub>A
                           snd (RTS.Unpack (A.Hom b c) (A.Hom a b) t)))
                         t"
              proof (cases "U.A.arr t")
                show "\<not> U.A.arr t \<Longrightarrow> ?thesis"
                  using a b c U.extensional F.extensional A.HOM_null_char
                        A.H.null_is_zero(2) A.null_coincidence sub_rts_resid_eq
                        HOM\<^sub>B_ac.null_char
                  by auto
                assume t: "U.A.arr t"
                have "HOM_ac.arr (fst (RTS.Unpack (A.Hom b c) (A.Hom a b) t) \<star>\<^sub>A
                                  snd (RTS.Unpack (A.Hom b c) (A.Hom a b) t))"
                  by (meson A.H.comp_in_homI A.HOM_arr_char HOM_bc_x_HOM_ab.arr_char
                      U.preserves_reflects_arr a b c t)
                thus ?thesis
                  using a b c t sub_rts_resid_eq F.preserves_reflects_arr
                  by auto
              qed
            qed
            also have "... = RTS.Map (F\<^sub>a a c) \<circ> RTS.Map (A.Comp a b c)"
              using a b c F\<^sub>a_def [of a c] A.Comp_def [of a b c] sub_rts_resid_eq
              apply simp
              using 1 RTS.bij_mkarr(3) by force
            also have "... = RTS.Map (F\<^sub>a a c \<cdot> A.Comp a b c)"
              using RTS.Map_comp
              by (simp add: \<open>RTS.par
                               (B.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b))
                               (F\<^sub>a a c \<cdot> A.Comp a b c)\<close>)
            finally show ?thesis by blast
          qed
        qed
      qed
    qed

  end

section "Equivalence of RTS-Enriched Categories and RTS-Categories"

  text\<open>
    We now extend to an equivalence the correspondence between categories enriched
    in \<open>\<^bold>R\<^bold>T\<^bold>S\<close> and RTS-categories.
  \<close>

subsection "RTS-Category to Enriched Category to RTS-Category"

  context enriched_category_of_rts_category
  begin

    interpretation RC: rts_category_of_enriched_category arr_type
                         Obj Hom Id Comp ..

    no_notation RTS.prod     (infixr \<open>\<otimes>\<close> 51)

    interpretation Trn: simulation RC.resid resid
                         \<open>\<lambda>t. if RC.arr t then RC.Trn t else null\<close>
    proof
      let ?Trn = "\<lambda>t. if RC.arr t then RC.Trn t else null"
      show "\<And>t. \<not> RC.arr t \<Longrightarrow> ?Trn t = null"
       by simp
      fix t u
      assume tu: "RC.V.con t u"
      interpret Hom: sub_rts resid \<open>\<lambda>v. H.in_hom v (RC.Dom u) (RC.Cod u)\<close>
        using sub_rts_HOM by auto
      interpret HOM: hom_rts arr_type Obj Hom Id Comp
                       \<open>RC.Dom u\<close> \<open>RC.Cod u\<close>
        using tu RC.con_char RC.arr_char RC.V.con_implies_arr
        by unfold_locales blast+
      show con: "?Trn t \<frown> ?Trn u"
      proof -
        have "HOM.con (RC.Trn t) (RC.Trn u) \<longleftrightarrow>
              Hom.con (RC.Trn t) (RC.Trn u)"
          using tu Hom.con_char Hom_def RC.con_char RTS.bij_mkide(3) by auto
        thus ?thesis
          using tu Hom.con_char RC.con_char RC.Con_def by auto
      qed
      show "?Trn (RC.resid t u) = ?Trn t \\ ?Trn u"
      proof -
        have "HOM\<^sub>E\<^sub>C (RC.Dom t) (RC.Cod t) (RC.Trn t) (RC.Trn u) =
              RC.Trn t \\ RC.Trn u"
          using tu con RC.con_char Hom.con_char Hom_def Hom.resid_def RC.arr_char
                RTS.bij_mkide(3)
          by auto
        thus ?thesis
          using tu con by auto
      qed
    qed

    interpretation MkArr: simulation resid RC.resid
                            \<open>\<lambda>t. if arr t then RC.MkArr (H.dom t) (H.cod t) t
                                 else RC.null\<close>
    proof
      let ?MkArr = "\<lambda>t. if arr t then RC.MkArr (H.dom t) (H.cod t) t else RC.null"
      show "\<And>t. \<not> arr t \<Longrightarrow> ?MkArr t = RC.null"
        by simp
      fix t u
      assume tu: "t \<frown> u"
      interpret Hom: sub_rts resid \<open>\<lambda>t. H.in_hom t (H.dom u) (H.cod u)\<close>
        using tu sub_rts_HOM [of "H.dom u" "H.cod u"] arr_coincidence V.con_implies_arr
        by auto
      show con: "RC.V.con (?MkArr t) (?MkArr u)"
        using tu V.con_implies_arr arr_coincidence RC.con_char HOM_arr_char
              con_implies_hpar Hom.con_char H.in_homI HOM_agreement
        by (unfold RC.con_char) auto
      show "?MkArr (t \\ u) = RC.resid (?MkArr t) (?MkArr u)"
        using tu con arr_coincidence con_implies_hpar RC.con_char HOM_arr_char
              con_implies_hpar Hom.con_char H.in_homI HOM_agreement Hom.resid_def
        apply auto[1]
          apply (metis VV.F.preserves_trg dom_trg V.trg_def)
        by (metis VV.G.preserves_trg cod_trg V.trg_def)
    qed

    interpretation Trn_MkArr: inverse_simulations resid RC.resid
                                \<open>\<lambda>t. if RC.arr t then RC.Trn t else null\<close>
                                \<open>\<lambda>t. if arr t then RC.MkArr (H.dom t) (H.cod t) t
                                     else RC.null\<close>
    proof
      let ?Trn = "\<lambda>t. if RC.arr t then RC.Trn t else null"
      let ?MkArr = "\<lambda>t. if arr t then RC.MkArr (H.dom t) (H.cod t) t else RC.null"
      show "?MkArr \<circ> ?Trn = I RC.resid"
      proof
        fix t
        show "(?MkArr \<circ> ?Trn) t = I RC.resid t"
          apply auto[1]
          by (metis RC.Cod.simps(1) RC.Dom.simps(1) RC.Trn.simps(1)
              RC.arr.simps(2) RC.arr_char RC.arr_eqI RC.null_char H.in_homE
              HOM_arr_char)
      qed
      show "?Trn \<circ> ?MkArr = I resid" by auto
    qed

    lemma inverse_simulations_Trn_MkArr:
    shows "inverse_simulations resid RC.resid
             (\<lambda>t. if RC.arr t then RC.Trn t else null)
             (\<lambda>t. if arr t then RC.MkArr (H.dom t) (H.cod t) t else RC.null)"
      ..

    interpretation Trn: "functor" RC.hcomp hcomp
                           \<open>\<lambda>t. if RC.arr t then RC.Trn t else null\<close>
    proof
      let ?Trn = "\<lambda>t. if RC.arr t then RC.Trn t else null"
      show "\<And>f. \<not> RC.H.arr f \<Longrightarrow> ?Trn f = H.null"
        using null_coincidence RC.arr_coincidence by auto
      show 1: "\<And>f. RC.H.arr f \<Longrightarrow> H.arr (?Trn f)"
        using RC.arr_coincidence arr_coincidence null_coincidence Trn.extensional
        by (metis Trn.preserves_reflects_arr)
      show "\<And>f. RC.H.arr f \<Longrightarrow> H.dom (?Trn f) = ?Trn (RC.H.dom f)"
      proof -
        fix t
        assume t: "RC.H.arr t"
        have 2: "RC.arr (RC.MkArr (RC.Dom t) (RC.Dom t) (RC.Dom t))"
          using t RC.arr_coincidence RC.arr_char HOM_arr_char H.ide_in_hom
          by auto
        show "H.dom (?Trn t) = ?Trn (RC.H.dom t)"
        proof (intro H.dom_eqI)
          show 3: "H.ide (?Trn (RC.H.dom t))"
            using t 2 RC.arr_coincidence Id_def RC.arr_char
                  RTS.One.arr_char RTS.One.is_extensional_rts
                  RTS.One.small_rts_axioms RTS.bij_mkarr(3)
            by (auto simp add: RC.H_dom_simp RC.H_cod_simp)
          show "H.seq (?Trn t) (?Trn (RC.H.dom t))"
            by (metis 3 H.ide_char H.seqI RC.Dom.simps(1) RC.H_dom_simp
                RC.arr_coincidence Trn.preserves_reflects_arr
                Trn_MkArr.inv_simp arr_coincidence t)
        qed
      qed
      show "\<And>f. RC.H.arr f \<Longrightarrow> H.cod (?Trn f) = ?Trn (RC.H.cod f)"
      proof -
        fix t
        assume t: "RC.H.arr t"
        have 2: "RC.arr (RC.MkArr (RC.Cod t) (RC.Cod t) (RC.Cod t))"
          using t RC.arr_coincidence RC.arr_char HOM_arr_char H.ide_in_hom
          by auto
        show "H.cod (?Trn t) = ?Trn (RC.H.cod t)"
        proof (intro H.cod_eqI)
          show 3: "H.ide (?Trn (RC.H.cod t))"
            using t 2 RC.arr_coincidence Id_def RC.arr_char
                  RTS.One.arr_char RTS.One.is_extensional_rts
                  RTS.One.small_rts_axioms RTS.bij_mkarr(3)
            by (auto simp add: RC.H_dom_simp RC.H_cod_simp)
          show "H.seq (?Trn (RC.H.cod t)) (?Trn t)"
            by (metis 1 3 H.ide_char H.seqI RC.Cod.simps(1)
                RC.H_cod_simp Trn.preserves_reflects_arr
                Trn_MkArr.inv_simp arr_coincidence t)
        qed
      qed
      fix f g
      assume fg: "RC.H.seq g f"
      interpret DOM: simulation
                       \<open>HOM\<^sub>E\<^sub>C (RC.Dom f) (RC.Cod f)\<close>
                       \<open>RTS.Rts (RTS.cod (Hom (RC.Dom f) (RC.Cod f)))\<close>
                       \<open>RTS.Map (Hom (RC.Dom f) (RC.Cod f))\<close>
        using fg ide_Hom RTS.ide_char RTS.arrD
        by (metis (no_types, lifting) RC.H.seqE RC.H_arr_char)
      interpret COD: simulation \<open>HOM\<^sub>E\<^sub>C (RC.Cod f) (RC.Cod g)\<close>
                       \<open>RTS.Rts (RTS.cod (Hom (RC.Cod f) (RC.Cod g)))\<close>
                       \<open>RTS.Map (Hom (RC.Cod f) (RC.Cod g))\<close>
        using fg ide_Hom RTS.ide_char RTS.arrD
        by (metis (no_types, lifting) RC.H.seqE RC.H_arr_char)
      interpret CODxDOM: product_rts
                           \<open>HOM\<^sub>E\<^sub>C (RC.Cod f) (RC.Cod g)\<close>
                           \<open>HOM\<^sub>E\<^sub>C (RC.Dom f) (RC.Cod f)\<close>
        ..
      interpret PU: inverse_simulations 
                      \<open>RTS.Rts
                         (RTS.dom
                            (Hom (RC.Cod f) (RC.Cod g) \<otimes>
                               Hom (RC.Dom f) (RC.Cod f)))\<close>
                      CODxDOM.resid
                      \<open>RTS.Pack
                         (Hom (RC.Cod f) (RC.Cod g))
                         (Hom (RC.Dom f) (RC.Cod f))\<close>
                      \<open>RTS.Unpack
                         (Hom (RC.Cod f) (RC.Cod g))
                         (Hom (RC.Dom f) (RC.Cod f))\<close>
        using fg RC.H_seq_char RC.arr_char
              RTS.inverse_simulations_Pack_Unpack
        by simp
      have 4: "COD.A.arr (RC.Trn g) \<and> DOM.A.arr (RC.Trn f)"
        using fg RC.arr_coincidence RC.H_arr_char
        by (elim RC.H.seqE) (auto simp add: RC.H_dom_simp RC.H_cod_simp)
      have "RTS.Unpack (Hom (RC.Cod f) (RC.Cod g)) (Hom (RC.Dom f) (RC.Cod f))
              (RTS.Pack (Hom (RC.Cod f) (RC.Cod g)) (Hom (RC.Dom f) (RC.Cod f))
                 (RC.Trn g, RC.Trn f)) =
            (RC.Trn g, RC.Trn f)"
        using PU.inv 4 by auto
      moreover have "RC.arr
                       (RC.MkArr (RC.Dom f) (RC.Cod g) (RC.Trn g \<star> RC.Trn f))"
        by (metis (no_types, lifting) 4 RC.H.seqE RC.H_arr_char RC.arr_MkArr
            H.comp_in_homI HOM_arr_char fg)
      ultimately show "?Trn (RC.hcomp g f) = hcomp (?Trn g) (?Trn f)"
        using fg RC.hcomp_def Comp_def PU.inv RC.arr_coincidence RTS.Map_mkarr
        apply auto[1]
        using RC.arr_char RTS.bij_mkarr(3) by force
    qed

    interpretation MkArr: "functor" hcomp RC.hcomp
                            \<open>\<lambda>t. if arr t then RC.MkArr (H.dom t) (H.cod t) t
                                 else RC.null\<close>
    proof
      let ?MkArr = "\<lambda>t. if arr t then RC.MkArr (H.dom t) (H.cod t) t
                        else RC.null"
      show "\<And>f. \<not> H.arr f \<Longrightarrow> ?MkArr f = RC.H.null"
        using arr_coincidence RC.null_coincidence by auto
      show "\<And>f. H.arr f \<Longrightarrow> RC.H.arr (?MkArr f)"
        using arr_coincidence RC.arr_coincidence
        by (metis MkArr.preserves_reflects_arr)
      have 1: "\<And>f. H.arr f \<Longrightarrow> RC.arr (RC.MkArr (H.dom f) (H.cod f) f)"
        using MkArr.preserves_reflects_arr arr_coincidence H.in_homI HOM_arr_char
        by (intro RC.arr_MkArr) auto
      thus "\<And>f. H.arr f \<Longrightarrow> RC.H.dom (?MkArr f) = ?MkArr (H.dom f)"
        using RC.H_dom_char Id_def RTS.One.arr_char RTS.One.is_extensional_rts
              RTS.One.small_rts_axioms RTS.bij_mkarr(3)
        by auto
      show "\<And>f. H.arr f \<Longrightarrow> RC.H.cod (?MkArr f) = ?MkArr (H.cod f)"
        using 1 RC.H_cod_char Id_def RTS.One.arr_char RTS.One.is_extensional_rts
              RTS.One.small_rts_axioms RTS.bij_mkarr(3)
        by auto
      show "\<And>g f. H.seq g f \<Longrightarrow>
                     ?MkArr (g \<star> f) = RC.hcomp (?MkArr g) (?MkArr f)"
      proof -
        fix f g
        assume fg: "H.seq g f"
        interpret COD: extensional_rts \<open>RTS.Rts (Hom (H.cod f) (H.cod g))\<close>
          using fg ide_Hom [of "H.cod f" "H.cod g"] arr_coincidence
          by (metis H.ide_cod H.seqE RTS.ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C(1) mem_Collect_eq)
        interpret DOM: extensional_rts \<open>RTS.Rts (Hom (H.dom f) (H.cod f))\<close>
          using fg ide_Hom [of "H.dom f" "H.cod f"] arr_coincidence
          by (metis H.ide_dom H.seqE RTS.ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C(1) mem_Collect_eq)
        interpret CODxDOM: product_rts
                             \<open>RTS.Rts (Hom (H.cod f) (H.cod g))\<close>
                             \<open>RTS.Rts (Hom (H.dom f) (H.cod f))\<close>
          ..
        show "?MkArr (g \<star> f) = RC.hcomp (?MkArr g) (?MkArr f)"
        proof -
          have "RC.hcomp (?MkArr g) (?MkArr f) =
                RC.MkArr (dom f) (cod g)
                  (RTS.Map (Comp (dom f) (cod f) (cod g))
                    (RTS.Pack
                       (Hom (cod f) (cod g)) (Hom (dom f) (cod f)) (g, f)))"
            using fg RC.hcomp_def [of "?MkArr g" "?MkArr f"] H.seqE by auto
          also have "... = RC.MkArr (dom f) (cod g) (g \<star> f)"
            by (metis 1 CODxDOM.arr_char H.seqE RC.Cod.simps(1)
                RC.Dom.simps(1) RC.Trn.simps(1) RC.arr_char Map_Comp_Pack
                fg fst_conv snd_conv)
          also have "... = ?MkArr (g \<star> f)"
            using fg by simp
          finally show ?thesis by simp
        qed
      qed
    qed

    interpretation Trn_MkArr: inverse_functors hcomp RC.hcomp
                               \<open>\<lambda>t. if RC.arr t then RC.Trn t else null\<close>
                               \<open>\<lambda>t. if arr t
                                    then RC.MkArr (H.dom t) (H.cod t) t
                                    else RC.null\<close>
    proof
      let ?Trn = "\<lambda>t. if RC.arr t then RC.Trn t else null"
      let ?MkArr = "\<lambda>t. if arr t
                        then RC.MkArr (H.dom t) (H.cod t) t
                        else RC.null"
      show "?MkArr \<circ> ?Trn = RC.H.map"
        by (auto simp add: RC.H.map_def Trn_MkArr.inv)
      show "(?Trn \<circ> ?MkArr) = H.map"
        using arr_coincidence null_coincidence H.is_extensional by auto
    qed

    lemma inverse_functors_Trn_MkArr:
    shows "inverse_functors hcomp RC.hcomp
             (\<lambda>t. if RC.arr t then RC.Trn t else null)
             (\<lambda>t. if arr t then RC.MkArr (H.dom t) (H.cod t) t else RC.null)"
      ..

    proposition induces_rts_category_isomorphism:
    shows "rts_category_isomorphism resid hcomp RC.resid RC.hcomp
             (\<lambda>t. if arr t then RC.MkArr (H.dom t) (H.cod t) t else RC.null)"
      using Trn_MkArr.inverse_functors_axioms
            Trn_MkArr.inverse_simulations_axioms
      by unfold_locales auto

  end

subsection "Enriched Category to RTS-Category to Enriched Category"

  context rts_category_of_small_enriched_category
  begin

    text\<open>
      As it is easy to get lost in the types and definitions, we begin with a road map
      of the construction to be performed.
      We are given a small RTS-enriched category \<open>(Obj, Hom, Id, Comp)\<close> with objects at type \<open>'O\<close>
      and as base category the category \<open>\<^bold>R\<^bold>T\<^bold>S\<close> with arrow type \<open>'A rtscat.arr\<close>.
      From this, we constructed a ``global RTS'' \<open>R\<close> by stitching together all of the
      RTS's underlying the hom-objects.
      We then reduced the type of \<open>R\<close> by taking its image under an injective map on
      arrows, to obtain an isomorphic RTS \<open>R'\<close> at arrow type \<open>'A\<close>.
      The smallness assumption was used for this.
      Next, we will extend \<open>R'\<close> to a locally small RTS-category \<open>R''\<close> (new name is used to
      avoid name clashes within sublocales) by equipping it with the horizontal composition
      @{term hcomp'} derived from the composition of the originally given enriched category.
      From \<open>R''\<close> we then construct an RTS-enriched category \<open>(R''.Obj R''.Hom R''.Id R''.Comp)\<close>.
    \<close>

    interpretation R'': locally_small_rts_category R' hcomp'
      using is_locally_small_rts_category by blast

    interpretation R'': enriched_category_of_rts_category arr_type R' hcomp'
      ..

    text\<open>
      Our objective is now to construct a fully faithful RTS-enriched functor \<open>(F\<^sub>o, F\<^sub>a)\<close>,
      from the originally given RTS-enriched category \<open>(Obj, Hom, Id, Comp)\<close> to the newly
      constructed RTS-category \<open>(R''.Obj R''.Hom R''.Id R''.Comp)\<close>.
      Note that this makes sense, because, due to the type reduction from \<open>R'\<close> to \<open>R''\<close>,
      we have arranged for the base category of \<open>(R''.Obj R''.Hom R''.Id R''.Comp)\<close> to be the
      same category \<open>\<^bold>R\<^bold>T\<^bold>S\<close> as that of the originally given \<open>(Obj, Hom, Id, Comp)\<close>.
      The object map \<open>F\<^sub>o\<close> will take \<open>a \<in> Obj :: 'O set\<close> to
      \<open>DN (MkArr a a (RTS.Map (Id a) one)) \<in> R''.Obj :: 'A set\<close>.
      The arrow map \<open>F\<^sub>a\<close> will take each pair \<open>(a, b)\<close> of elements of \<open>Obj\<close> to an invertible
      arrow \<open>\<guillemotleft>F\<^sub>a a b : Hom a b \<rightarrow> R''.Hom (F\<^sub>o a) (F\<^sub>o b)\<guillemotright>\<close> of \<open>\<^bold>R\<^bold>T\<^bold>S\<close>.
      This arrow corresponds to the invertible simulation from \<open>HOM\<^sub>E\<^sub>C a b\<close> to
      \<open>R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)\<close> that takes \<open>t \<in> Hom a b\<close> to
      \<open>DN (MkArr a b t) \<in> R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)\<close>.
    \<close>

     abbreviation F\<^sub>o :: "'O \<Rightarrow> 'A"
     where "F\<^sub>o \<equiv> \<lambda>a. DN (MkArr a a (RTS.Map (Id a) RTS.One.the_arr))"

     abbreviation F\<^sub>a :: "'O \<Rightarrow> 'O \<Rightarrow> 'A rtscat.arr"
     where "F\<^sub>a \<equiv> \<lambda>a b. if a \<in> Obj \<and> b \<in> Obj
                       then RTS.mkarr (HOM\<^sub>E\<^sub>C a b) (R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b))
                              (\<lambda>t. if residuation.arr (HOM\<^sub>E\<^sub>C a b) t
                                   then DN (MkArr a b t)
                                   else ResiduatedTransitionSystem.partial_magma.null
                                         (R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)))
                       else RTS.null"

     lemma ide_F\<^sub>o:
     assumes "a \<in> Obj"
     shows "DN (MkArr a a (RTS.Map (Id a) RTS.One.the_arr)) \<in> Collect H'.ide"
       using H'_ide_char Id_yields_horiz_ide assms obj_implies_sta by auto

     lemma bij_F\<^sub>o:
     shows "bij_betw F\<^sub>o Obj R''.Obj"
     proof -
       have "bij_betw (DN \<circ> (\<lambda>A. MkArr A A (RTS.Map (Id A) RTS.One.the_arr)))
               Obj (Collect H'.ide)"
       proof -
         have "bij_betw DN (Collect H.ide) (Collect H'.ide)"
           using H'_ide_char H.ideD(1) H'.ideD(1)
           by (intro bij_betwI) auto
         thus ?thesis
           using bij_betw_Obj_horiz_ide bij_betw_trans by blast
       qed
       moreover
         have "DN \<circ> (\<lambda>A. MkArr A A (RTS.Map (Id A) RTS.One.the_arr)) = F\<^sub>o"
         by auto
       ultimately show ?thesis by simp
     qed

     lemma F\<^sub>a_in_hom [intro, simp]:
     assumes "a \<in> Obj" and "b \<in> Obj"
     shows "\<guillemotleft>F\<^sub>a a b : Hom a b \<rightarrow> R''.Hom (F\<^sub>o a) (F\<^sub>o b)\<guillemotright>"
     proof
       show "RTS.arr (F\<^sub>a a b)"
       proof -
         have "RTS.arr
                 ((RTS.mkarr (HOM\<^sub>E\<^sub>C a b) (R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b))
                     (\<lambda>t. if residuation.arr (HOM\<^sub>E\<^sub>C a b) t then DN (MkArr a b t)
                          else ResiduatedTransitionSystem.partial_magma.null
                                 (R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)))))"
         proof (intro RTS.arrI\<^sub>R\<^sub>T\<^sub>S\<^sub>C)
           interpret HOM: extensional_rts \<open>HOM\<^sub>E\<^sub>C a b\<close>
             using assms by simp
           interpret HOM': extensional_rts \<open>R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)\<close>
             using assms R''.ide_Hom RTS.ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C RTS.arrD
             by (metis (no_types, lifting) ide_F\<^sub>o)
           show "extensional_rts (HOM\<^sub>E\<^sub>C a b) \<and> small_rts (HOM\<^sub>E\<^sub>C a b)"
             using assms by simp
           show "extensional_rts (R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)) \<and>
                   small_rts (R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b))"
             using assms R''.ide_Hom RTS.ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C RTS.arrD
             by (metis (no_types, lifting) ide_F\<^sub>o)
           text\<open>
             To prove the rest we need information about \<open>R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)\<close>.
             Rather than just having it as an abstract RTS, we need to know that
             it is a sub-RTS of \<open>R'\<close>, which in turn is isomorphic (via DN)
             to the ``global RTS'' \<open>R\<close>, which has arrows of the form \<open>MkArr a b t\<close>.
           \<close>
           have *: "R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b) =
                    sub_rts.resid R' (\<lambda>t. H'.in_hom t (F\<^sub>o a) (F\<^sub>o b))"
             using assms R''.Hom_def [of "F\<^sub>o a" "F\<^sub>o b"] ide_F\<^sub>o RTS.bij_mkide(3)
             by simp
           interpret HOM'_alt: sub_rts R' \<open>\<lambda>t. H'.in_hom t (F\<^sub>o a) (F\<^sub>o b)\<close>
             using assms ide_F\<^sub>o R''.sub_rts_HOM by metis
           have "(\<lambda>t. if HOM.arr t then DN (MkArr a b t) else HOM'.null)
                   \<in> Collect (simulation (HOM\<^sub>E\<^sub>C a b) (R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)))"
           proof
             show "simulation (HOM\<^sub>E\<^sub>C a b) (R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b))
                     (\<lambda>t. if HOM.arr t then DN (MkArr a b t) else HOM'.null)"
             proof
               show "\<And>t. \<not> HOM.arr t \<Longrightarrow>
                             (if HOM.arr t then DN (MkArr a b t) else HOM'.null) =
                             HOM'.null"
                 by simp
               fix t u
               assume tu: "HOM.con t u"
               have 0: "V.con (MkArr a b t) (MkArr a b u)"
                 using tu Con_def
                 by (simp add: assms(1-2) con_char HOM.con_implies_arr(1-2))
               have 1: "R'.con (DN (MkArr a b t)) (DN (MkArr a b u))"
                 using 0 UP_DN.G.preserves_con by simp
               have 2: "HOM'_alt.con (DN (MkArr a b t)) (DN (MkArr a b u))"
               proof -
                 have "H'.in_hom (DN (MkArr a b t)) (F\<^sub>o a) (F\<^sub>o b)"
                 proof -
                   have "H.arr (UP (DN (MkArr a b t)))"
                     using "1" R'.con_implies_arr(1) by auto
                   thus ?thesis
                     using assms
                     by (simp add: H'.in_homI H'_cod_char H'_dom_char
                         H_cod_char H_dom_char)
                 qed
                 moreover have "H'.in_hom (DN (MkArr a b u)) (F\<^sub>o a) (F\<^sub>o b)"
                   by (metis (no_types, lifting) "1" H'.in_homE H'.in_homI
                       R''.con_implies_hpar calculation)
                 ultimately show ?thesis
                   using 1 HOM'_alt.con_char by blast
               qed
               show "HOM'.con (if HOM.arr t then DN (MkArr a b t) else HOM'.null)
                              (if HOM.arr u then DN (MkArr a b u) else HOM'.null)"
                 using tu * 2 HOM.con_implies_arr by auto
               show "(if HOM.arr (HOM\<^sub>E\<^sub>C a b t u)
                      then DN (MkArr a b (HOM\<^sub>E\<^sub>C a b t u))
                      else HOM'.null) =
                     R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)
                       (if HOM.arr t then DN (MkArr a b t) else HOM'.null)
                       (if HOM.arr u then DN (MkArr a b u) else HOM'.null)"
               proof -
                 have "(if HOM.arr (HOM\<^sub>E\<^sub>C a b t u)
                        then DN (MkArr a b (HOM\<^sub>E\<^sub>C a b t u))
                        else HOM'.null) =
                       HOM'_alt.resid
                         (if HOM.arr t then DN (MkArr a b t) else HOM'.null)
                         (if HOM.arr u then DN (MkArr a b u) else HOM'.null)"
                 proof -
                   have "H'.in_hom (DN (MkArr a b t)) (F\<^sub>o a) (F\<^sub>o b)"
                     using assms tu 2 HOM'_alt.con_char by fastforce
                   moreover have "H'.in_hom (DN (MkArr a b u)) (F\<^sub>o a) (F\<^sub>o b)"
                     using assms tu 2 HOM'_alt.con_char by fastforce
                   moreover have "R' (DN (MkArr a b t)) (DN (MkArr a b u)) =
                                  DN (MkArr a b (HOM\<^sub>E\<^sub>C a b t u))"
                     by (metis "0" Cod.simps(1) Dom.simps(1) Trn.simps(1)
                         UP_DN.G.preserves_resid con_char resid.simps(3))
                   ultimately show ?thesis
                     unfolding HOM'_alt.resid_def
                     using tu 1 HOM.con_implies_arr UP_DN.inv UP_DN.inv' by auto
                 qed
                 also have "... = R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)
                                    (if HOM.arr t then DN (MkArr a b t) else HOM'.null)
                                    (if HOM.arr u then DN (MkArr a b u) else HOM'.null)"
                   using * by simp
                 finally show ?thesis by simp
               qed
             qed
           qed
           thus "RTS.mkarr (HOM\<^sub>E\<^sub>C a b) (R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b))
                   (\<lambda>t. if HOM.arr t then DN (MkArr a b t) else HOM'.null)
                   \<in> RTS.mkarr (HOM\<^sub>E\<^sub>C a b) (R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)) `
                       Collect (simulation (HOM\<^sub>E\<^sub>C a b) (R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)))"
             by auto
         qed
         thus ?thesis
           using assms by simp
       qed
       show "RTS.dom (F\<^sub>a a b) = Hom a b"
         using assms(1-2) \<open>RTS.arr (F\<^sub>a a b)\<close> by auto
       show "RTS.cod (F\<^sub>a a b) = R''.Hom (F\<^sub>o a) (F\<^sub>o b)"
         using assms(1-2) \<open>RTS.arr (F\<^sub>a a b)\<close> ide_F\<^sub>o by auto
     qed

     lemma F\<^sub>a_simps [simp]:
     assumes "a \<in> Obj" and "b \<in> Obj"
     shows "RTS.arr (F\<^sub>a a b)"
     and "RTS.dom (F\<^sub>a a b) = Hom a b"
     and "RTS.cod (F\<^sub>a a b) = R''.Hom (F\<^sub>o a) (F\<^sub>o b)"
       using assms F\<^sub>a_in_hom by blast+

     lemma Map_F\<^sub>a_simp [simp]:
     assumes "a \<in> Obj" and "b \<in> Obj" and "residuation.arr (HOM\<^sub>E\<^sub>C a b) t"
     shows "RTS.Map (F\<^sub>a a b) t = DN (MkArr a b t)"
       using assms RTS.bij_mkarr(3) ide_F\<^sub>o by force

     interpretation \<Phi>: rts_enriched_functor
                          Obj Hom Id Comp R''.Obj R''.Hom R''.Id R''.Comp
                          F\<^sub>o F\<^sub>a
     proof
       show "\<And>a. a \<in> Obj \<Longrightarrow> F\<^sub>o a \<in> R''.Obj"
         using ide_F\<^sub>o by blast
       show "\<And>a b. \<lbrakk>a \<in> Obj; b \<in> Obj\<rbrakk> \<Longrightarrow>
                      \<guillemotleft>F\<^sub>a a b : Hom a b \<rightarrow> R''.Hom (F\<^sub>o a) (F\<^sub>o b)\<guillemotright>"
         using F\<^sub>a_in_hom by blast
       show "\<And>a b. a \<notin> Obj \<or> b \<notin> Obj \<Longrightarrow> F\<^sub>a a b = RTS.null"
         by auto
       show "\<And>a. a \<in> Obj \<Longrightarrow> F\<^sub>a a a \<cdot> Id a = R''.Id (F\<^sub>o a)"
       proof -
         fix a
         assume a: "a \<in> Obj"
         show "F\<^sub>a a a \<cdot> Id a = R''.Id (F\<^sub>o a)"
         proof (intro RTS.arr_eqI)
           show 1: "RTS.par (F\<^sub>a a a \<cdot> Id a) (R''.Id (F\<^sub>o a))"
             using a Id_in_hom R''.Id_in_hom F\<^sub>a_in_hom ide_F\<^sub>o RTS.in_homE
             apply (intro conjI)
                apply auto[1]
             by fastforce+
           show "RTS.Map (F\<^sub>a a a \<cdot> Id a) = RTS.Map (R''.Id (F\<^sub>o a))"
           proof -
             interpret Map_Id_a: simulation RTS.One.resid \<open>HOM\<^sub>E\<^sub>C a a\<close>
                                   \<open>RTS.Map (Id a)\<close>
               using a Id_in_hom [of a] RTS.arrD(3) [of "Id a"] RTS.unity_agreement
               by auto
             interpret Map_F\<^sub>a_aa: simulation
                                    \<open>HOM\<^sub>E\<^sub>C a a\<close> \<open>RTS.Rts (R''.Hom (F\<^sub>o a) (F\<^sub>o a))\<close>
                                    \<open>RTS.Map (F\<^sub>a a a)\<close>
               using a F\<^sub>a_in_hom [of a a] RTS.arrD(3) by fastforce
             interpret Map_F\<^sub>a_aa_o_Map_Id_a: simulation
                                               RTS.One.resid
                                               \<open>RTS.Rts (R''.Hom (F\<^sub>o a) (F\<^sub>o a))\<close>
                                               \<open>RTS.Map (F\<^sub>a a a) \<circ> RTS.Map (Id a)\<close>
               using simulation_comp Map_Id_a.simulation_axioms
                     Map_F\<^sub>a_aa.simulation_axioms
               by blast
             interpret Map_R''_Id_F\<^sub>o_a: simulation
                                          RTS.One.resid
                                          \<open>RTS.Rts (R''.Hom (F\<^sub>o a) (F\<^sub>o a))\<close>
                                          \<open>RTS.Map (R''.Id (F\<^sub>o a))\<close>
               using a
               by (metis (no_types, lifting) R''.Id_in_hom RTS.Rts_one RTS.arrD(3)
                   RTS.in_homE RTS.unity_agreement ide_F\<^sub>o)
             have "RTS.Map (F\<^sub>a a a \<cdot> Id a) = RTS.Map (F\<^sub>a a a) \<circ> RTS.Map (Id a)"
               using 1 RTS.Map_comp by blast
             also have "... = RTS.Map (R''.Id (F\<^sub>o a))"
               using Map_Id_a.preserves_reflects_arr Map_R''_Id_F\<^sub>o_a.extensional
                     R''.Id_def RTS.One.arr_char RTS.One.is_extensional_rts
                     RTS.One.small_rts_axioms RTS.bij_mkarr(3) a ide_F\<^sub>o
               by auto
             finally show ?thesis by blast
           qed
         qed
       qed
       show "\<And>a b c. \<lbrakk>a \<in> Obj; b \<in> Obj; c \<in> Obj\<rbrakk> \<Longrightarrow>
                        R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b) =
                        F\<^sub>a a c \<cdot> Comp a b c"
       proof -
         fix a b c
         assume a: "a \<in> Obj" and b: "b \<in> Obj" and c: "c \<in> Obj"
         show "R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b) =
               F\<^sub>a a c \<cdot> Comp a b c"
         proof (intro RTS.arr_eqI)
           show 1: "RTS.par
                      (R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b))
                      (F\<^sub>a a c \<cdot> Comp a b c)"
           proof (intro conjI)
             show 2: "RTS.seq (R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c)) (F\<^sub>a b c \<otimes> F\<^sub>a a b)"
               using a b c F\<^sub>a_in_hom ide_F\<^sub>o R''.Comp_in_hom R''.Hom_def by blast
             show 3: "RTS.seq (F\<^sub>a a c) (Comp a b c)"
               using a b c F\<^sub>a_in_hom ide_F\<^sub>o R''.Comp_in_hom R''.Hom_def by blast
             show "RTS.dom (R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b)) =
                   RTS.dom (F\<^sub>a a c \<cdot> Comp a b c)"
             proof -
               have "RTS.dom (R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b)) =
                     RTS.dom (F\<^sub>a b c \<otimes> F\<^sub>a a b)"
                 using a b c 2 R''.Comp_in_hom by auto
               also have "... = Hom b c \<otimes> Hom a b"
                 using a b c F\<^sub>a_in_hom
                 by (meson RTS.CMC.dom_tensor)
               also have "... = RTS.dom (F\<^sub>a a c \<cdot> Comp a b c)"
                 using a b c 3 Comp_in_hom [of a b c] by auto
               finally show ?thesis by blast
             qed
             show "RTS.cod (R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b)) =
                   RTS.cod (F\<^sub>a a c \<cdot> Comp a b c)"
             proof -
               have "RTS.cod (R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b)) =
                     RTS.cod (R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c))"
                 using a b c 2 F\<^sub>a_in_hom R''.Comp_in_hom by auto
               also have "... = RTS.cod (F\<^sub>a a c \<cdot> Comp a b c)"
                 using a b c 3 ide_F\<^sub>o R''.Comp_in_hom by auto
               finally show ?thesis by blast
             qed
           qed
           show "RTS.Map (R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b)) =
                 RTS.Map (F\<^sub>a a c \<cdot> Comp a b c)"
           proof
             interpret Dom_bc: extensional_rts \<open>HOM\<^sub>E\<^sub>C b c\<close>
               using b c by simp
             interpret Dom_ab: extensional_rts \<open>HOM\<^sub>E\<^sub>C a b\<close>
               using a b by simp
             interpret Dom_bc_X_Dom_ab: product_rts \<open>HOM\<^sub>E\<^sub>C b c\<close> \<open>HOM\<^sub>E\<^sub>C a b\<close>
               ..
             interpret Dom_bcxab: extensional_rts \<open>RTS.Rts (Hom b c \<otimes> Hom a b)\<close>
               using a b c by simp
             have 3: "RTS.ide (RTS.dom (F\<^sub>a b c)) \<and> RTS.ide (RTS.dom (F\<^sub>a a b))"
               using a b c F\<^sub>a_in_hom RTS.ide_dom by blast
             have 4: "RTS.ide (RTS.cod (F\<^sub>a b c)) \<and> RTS.ide (RTS.cod (F\<^sub>a a b))"
               using a b c F\<^sub>a_in_hom RTS.ide_cod by blast
             interpret Cod_bc: extensional_rts \<open>RTS.Rts (RTS.cod (F\<^sub>a b c))\<close>
               using 4 RTS.ide_char RTS.arrD RTS.arr_cod_iff_arr
               by (metis (no_types, lifting))
             interpret Cod_ab: extensional_rts \<open>RTS.Rts (RTS.cod (F\<^sub>a a b))\<close>
               using 4 RTS.ide_char RTS.arrD RTS.arr_cod_iff_arr
               by (metis (no_types, lifting))
             interpret Cod_bc_X_Cod_ab: product_rts
                                          \<open>RTS.Rts (RTS.cod (F\<^sub>a b c))\<close>
                                          \<open>RTS.Rts (RTS.cod (F\<^sub>a a b))\<close>
               ..
             interpret F\<^sub>abc: simulation \<open>HOM\<^sub>E\<^sub>C b c\<close>
                               \<open>RTS.Rts (RTS.cod (F\<^sub>a b c))\<close>
                               \<open>RTS.Map (F\<^sub>a b c)\<close>
               using b c F\<^sub>a_in_hom [of b c] RTS.arrD(3) [of "F\<^sub>a b c"] by auto
             interpret F\<^sub>aab: simulation \<open>HOM\<^sub>E\<^sub>C a b\<close>
                               \<open>RTS.Rts (RTS.cod (F\<^sub>a a b))\<close>
                               \<open>RTS.Map (F\<^sub>a a b)\<close>
               using a b F\<^sub>a_in_hom [of a b] RTS.arrD(3) [of "F\<^sub>a a b"] by auto
             interpret F\<^sub>abc_X_F\<^sub>aab: product_simulation
                                     \<open>HOM\<^sub>E\<^sub>C b c\<close> \<open>HOM\<^sub>E\<^sub>C a b\<close>
                                     \<open>RTS.Rts (RTS.cod (F\<^sub>a b c))\<close>
                                     \<open>RTS.Rts (RTS.cod (F\<^sub>a a b))\<close>
                                     \<open>RTS.Map (F\<^sub>a b c)\<close> \<open>RTS.Map (F\<^sub>a a b)\<close>
               ..
             interpret U: simulation
                            \<open>RTS.Rts (Hom b c \<otimes> Hom a b)\<close>
                            Dom_bc_X_Dom_ab.resid
                            \<open>RTS.Unpack (RTS.dom (F\<^sub>a b c)) (RTS.dom (F\<^sub>a a b))\<close>
             proof -
               have "RTS.arr (F\<^sub>a b c) \<and> RTS.arr (F\<^sub>a a b)"
                 using a b c F\<^sub>a_in_hom by blast
               thus "simulation
                       (RTS.Rts (Hom b c \<otimes> Hom a b))
                       Dom_bc_X_Dom_ab.resid
                       (RTS.Unpack (RTS.dom (F\<^sub>a b c)) (RTS.dom (F\<^sub>a a b)))"
                 using a b c 1 F\<^sub>a_in_hom
                       RTS.simulation_Unpack [of "Hom b c" "Hom a b"]
                 by fastforce
             qed
             fix x
             show "RTS.Map
                     (R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b)) x =
                   RTS.Map (F\<^sub>a a c \<cdot> Comp a b c) x"
             proof (cases "Dom_bcxab.arr x")
               show "\<not> Dom_bcxab.arr x \<Longrightarrow>
                       RTS.Map
                         (R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b)) x =
                       RTS.Map (F\<^sub>a a c \<cdot> Comp a b c) x"
               proof -
                 interpret LHS: simulation
                                  \<open>RTS.Rts (Hom b c \<otimes> Hom a b)\<close>
                                  \<open>R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o c)\<close>
                                  \<open>RTS.Map
                                     (R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot>
                                        (F\<^sub>a b c \<otimes> F\<^sub>a a b))\<close>
                 proof -
                   have "RTS.seq (R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c)) (F\<^sub>a b c \<otimes> F\<^sub>a a b)"
                     using a b c 1 ide_F\<^sub>o by force
                   moreover have "RTS.Dom
                                    (R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot>
                                       (F\<^sub>a b c \<otimes> F\<^sub>a a b)) =
                                  RTS.Rts (Hom b c \<otimes> Hom a b)"
                     using a b c 1 ide_F\<^sub>o R''.ide_Hom R''.Comp_in_hom
                     by (metis (no_types, lifting) Comp_in_hom RTS.dom_comp
                         RTS.in_homE)
                   moreover have "RTS.Cod
                                    (R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot>
                                       (F\<^sub>a b c \<otimes> F\<^sub>a a b)) =
                                  R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o c)"
                     using a b c 1 ide_F\<^sub>o R''.ide_Hom R''.Comp_in_hom
                     by (metis (no_types, lifting) R''.Comp_simps(3) RTS.cod_comp)
                   ultimately
                   show "simulation
                           (RTS.Rts
                              (Hom b c \<otimes> Hom a b)) (R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o c))
                           (RTS.Map
                              (R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b)))"
                     using a b c 1 ide_F\<^sub>o
                           RTS.arrD(3)
                             [of "R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b)"]
                     by auto
                 qed
                 interpret RHS: simulation
                                  \<open>RTS.Rts (Hom b c \<otimes> Hom a b)\<close>
                                  \<open>R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o c)\<close>
                                  \<open>RTS.Map (F\<^sub>a a c \<cdot> Comp a b c)\<close>
                 proof -
                   have "RTS.seq (F\<^sub>a a c) (Comp a b c)"
                     using a b c 1 ide_F\<^sub>o by force
                   moreover have "RTS.Dom (F\<^sub>a a c \<cdot> Comp a b c) =
                                  RTS.Rts (Hom b c \<otimes> Hom a b)"
                     using a b c 1 ide_F\<^sub>o R''.ide_Hom R''.Comp_in_hom
                     by (metis (no_types, lifting) Comp_in_hom RTS.dom_comp
                         RTS.in_homE)
                   moreover have "RTS.Cod (F\<^sub>a a c \<cdot> Comp a b c) =
                                  R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o c)"
                     using a b c 1 ide_F\<^sub>o R''.ide_Hom R''.Comp_in_hom
                     by (metis (no_types, lifting) R''.Comp_simps(3) RTS.cod_comp)
                  ultimately
                   show "simulation
                           (RTS.Rts
                              (Hom b c \<otimes> Hom a b)) (R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o c))
                           (RTS.Map (F\<^sub>a a c \<cdot> Comp a b c))"
                     using a b c 1 ide_F\<^sub>o
                           RTS.arrD(3) [of "F\<^sub>a a c \<cdot> Comp a b c"]
                     by auto
                 qed
                 assume x: "\<not> Dom_bcxab.arr x"
                 show "RTS.Map
                         (R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b)) x =
                       RTS.Map (F\<^sub>a a c \<cdot> Comp a b c) x"
                   using x LHS.extensional RHS.extensional by presburger
               qed
               assume x: "Dom_bcxab.arr x"
               have 0: "Dom_bc_X_Dom_ab.arr (RTS.Unpack (Hom b c) (Hom a b) x)"
                 using a b c x U.preserves_reflects_arr [of x]
                       F\<^sub>a_in_hom [of b c] F\<^sub>a_in_hom [of a b]
                       Dom_bc_X_Dom_ab.arr_char
                 by (metis (no_types, lifting) RTS.in_homE)

               have "RTS.Map
                       (R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c) \<cdot> (F\<^sub>a b c \<otimes> F\<^sub>a a b)) x =
                     RTS.Map
                       (R''.Comp (F\<^sub>o a) (F\<^sub>o b) (F\<^sub>o c))
                       (RTS.Map (F\<^sub>a b c \<otimes> F\<^sub>a a b) x)"
                 using a b c 1 ide_F\<^sub>o RTS.Map_comp by auto
               also have "... =
                          fst (RTS.Unpack
                                 (R''.Hom (F\<^sub>o b) (F\<^sub>o c)) (R''.Hom (F\<^sub>o a) (F\<^sub>o b))
                                    (RTS.Map (F\<^sub>a b c \<otimes> F\<^sub>a a b) x)) \<star>\<acute>
                            snd (RTS.Unpack
                                   (R''.Hom (F\<^sub>o b) (F\<^sub>o c))
                                   (R''.Hom (F\<^sub>o a) (F\<^sub>o b))
                                   (RTS.Map (F\<^sub>a b c \<otimes> F\<^sub>a a b) x))"
                 using a b c R''.Comp_def RTS.bij_mkarr(3)
                       \<open>\<And>a. a \<in> Obj \<Longrightarrow> F\<^sub>o a \<in> R''.Obj\<close>
                 by force
               also have "... =
                          fst (RTS.Unpack (RTS.cod (F\<^sub>a b c)) (RTS.cod (F\<^sub>a a b))
                                 (RTS.Map (F\<^sub>a b c \<otimes> F\<^sub>a a b) x)) \<star>\<acute>
                            snd (RTS.Unpack (RTS.cod (F\<^sub>a b c)) (RTS.cod (F\<^sub>a a b))
                                   (RTS.Map (F\<^sub>a b c \<otimes> F\<^sub>a a b) x))"
               proof -
                 have "R''.Hom (F\<^sub>o b) (F\<^sub>o c) = RTS.cod (F\<^sub>a b c)"
                   using a b c ide_F\<^sub>o F\<^sub>a_in_hom R''.Hom_def by force
                 moreover have "R''.Hom (F\<^sub>o a) (F\<^sub>o b) = RTS.cod (F\<^sub>a a b)"
                   using a b c ide_F\<^sub>o F\<^sub>a_in_hom R''.Hom_def by force
                 ultimately show ?thesis by argo
               qed
               also have "... =
                          fst
                            (RTS.Unpack (RTS.cod (F\<^sub>a b c)) (RTS.cod (F\<^sub>a a b))
                               ((RTS.Pack (RTS.cod (F\<^sub>a b c)) (RTS.cod (F\<^sub>a a b)) \<circ>
                                   product_simulation.map
                                     (HOM\<^sub>E\<^sub>C b c) (HOM\<^sub>E\<^sub>C a b)
                                     (RTS.Map (F\<^sub>a b c)) (RTS.Map (F\<^sub>a a b)) \<circ>
                                       RTS.Unpack
                                         (RTS.dom (F\<^sub>a b c)) (RTS.dom (F\<^sub>a a b))) x)) \<star>\<acute>
                            snd
                              (RTS.Unpack (RTS.cod (F\<^sub>a b c)) (RTS.cod (F\<^sub>a a b))
                                 ((RTS.Pack (RTS.cod (F\<^sub>a b c)) (RTS.cod (F\<^sub>a a b)) \<circ>
                                     F\<^sub>abc_X_F\<^sub>aab.map \<circ>
                                        RTS.Unpack
                                          (RTS.dom (F\<^sub>a b c)) (RTS.dom (F\<^sub>a a b))) x))"
               proof -
                 have "RTS.Map (F\<^sub>a b c \<otimes> F\<^sub>a a b) =
                       RTS.Pack (RTS.cod (F\<^sub>a b c)) (RTS.cod (F\<^sub>a a b)) \<circ>
                         product_simulation.map
                           (RTS.Dom (F\<^sub>a b c)) (RTS.Dom (F\<^sub>a a b))
                           (RTS.Map (F\<^sub>a b c)) (RTS.Map (F\<^sub>a a b)) \<circ>
                              RTS.Unpack (RTS.dom (F\<^sub>a b c)) (RTS.dom (F\<^sub>a a b))"
                   using a b c 4 RTS.Map_prod [of "F\<^sub>a b c" "F\<^sub>a a b"] F\<^sub>a_in_hom
                   by (metis (no_types, lifting) RTS.arr_cod_iff_arr RTS.ideD(1)
                       RTS.tensor_agreement)
                 moreover have "RTS.Dom (F\<^sub>a b c) = HOM\<^sub>E\<^sub>C b c \<and>
                                  RTS.Dom (F\<^sub>a a b) = HOM\<^sub>E\<^sub>C a b"
                   using a b c F\<^sub>a_in_hom [of b c] F\<^sub>a_in_hom [of a b] by auto
                 ultimately show ?thesis by simp
               qed
               also have "... =
                          fst (RTS.Unpack (RTS.cod (F\<^sub>a b c)) (RTS.cod (F\<^sub>a a b))
                                 (RTS.Pack (RTS.cod (F\<^sub>a b c)) (RTS.cod (F\<^sub>a a b))
                                    (F\<^sub>abc_X_F\<^sub>aab.map
                                      (RTS.Unpack (Hom b c) (Hom a b) x)))) \<star>\<acute>
                          snd (RTS.Unpack (RTS.cod (F\<^sub>a b c)) (RTS.cod (F\<^sub>a a b))
                                (RTS.Pack (RTS.cod (F\<^sub>a b c)) (RTS.cod (F\<^sub>a a b))
                                    (F\<^sub>abc_X_F\<^sub>aab.map
                                      (RTS.Unpack (Hom b c) (Hom a b) x))))"
                 using a b c F\<^sub>a_in_hom [of b c] F\<^sub>a_in_hom [of a b] by fastforce
               also have "... =
                          fst
                            (F\<^sub>abc_X_F\<^sub>aab.map
                               (RTS.Unpack (Hom b c) (Hom a b) x)) \<star>\<acute>
                          snd
                            (F\<^sub>abc_X_F\<^sub>aab.map
                               (RTS.Unpack (Hom b c) (Hom a b) x))"
               proof -
                 have 1: "RTS.ide (RTS.cod (F\<^sub>a b c)) \<and> RTS.ide (RTS.cod (F\<^sub>a a b))"
                   using a b c F\<^sub>a_in_hom RTS.ide_cod by blast
                 interpret PU: inverse_simulations
                                 \<open>RTS.Rts (RTS.cod (F\<^sub>a b c) \<otimes> RTS.cod (F\<^sub>a a b))\<close>
                                 Cod_bc_X_Cod_ab.resid
                                 \<open>RTS.Pack (RTS.cod (F\<^sub>a b c)) (RTS.cod (F\<^sub>a a b))\<close>
                                 \<open>RTS.Unpack (RTS.cod (F\<^sub>a b c)) (RTS.cod (F\<^sub>a a b))\<close>
                   using a b c 1 F\<^sub>a_in_hom [of a b] F\<^sub>a_in_hom [of b c]
                         RTS.inverse_simulations_Pack_Unpack
                   by fastforce
                 show ?thesis
                 proof -
                   have "Cod_bc_X_Cod_ab.arr
                           (F\<^sub>abc_X_F\<^sub>aab.map
                              (RTS.Unpack (Hom b c) (Hom a b) x))"
                     using a b c x U.preserves_reflects_arr
                           F\<^sub>a_in_hom [of b c] F\<^sub>a_in_hom [of a b]
                     by fastforce
                   thus ?thesis by simp
                 qed
               qed
               also have "... =
                          RTS.Map (F\<^sub>a b c)
                            (fst (RTS.Unpack (Hom b c) (Hom a b) x)) \<star>\<acute>
                          RTS.Map
                            (F\<^sub>a a b) (snd (RTS.Unpack (Hom b c) (Hom a b) x))"
                 using 0 F\<^sub>abc_X_F\<^sub>aab.map_def by auto
               also have "... =
                          DN (MkArr b c
                                (fst (RTS.Unpack (Hom b c) (Hom a b) x))) \<star>\<acute>
                          DN (MkArr a b
                                (snd (RTS.Unpack (Hom b c) (Hom a b) x)))"
                 using a b c 0 Map_F\<^sub>a_simp by auto
               also have "... =
                          DN (MkArr b c (fst (RTS.Unpack (Hom b c) (Hom a b) x)) \<star>
                                MkArr a b (snd (RTS.Unpack (Hom b c) (Hom a b) x)))"
                 using 0 a b c arr_MkArr by force
               also have "... =
                          DN (MkArr a c
                                (RTS.Map (Comp a b c)
                                   (RTS.Pack (Hom b c) (Hom a b)
                                      (RTS.Unpack (Hom b c) (Hom a b) x))))"
                 using 0 a b c x hcomp_def
                 by (simp add: arr_MkArr) 
               also have "... = DN (MkArr a c (RTS.Map (Comp a b c) x))"
               proof -
                 interpret PU: inverse_simulations
                                 \<open>RTS.Rts (Hom b c \<otimes> Hom a b)\<close>
                                 Dom_bc_X_Dom_ab.resid
                                 \<open>RTS.Pack (Hom b c) (Hom a b)\<close>
                                 \<open>RTS.Unpack (Hom b c) (Hom a b)\<close>
                   using a b c RTS.inverse_simulations_Pack_Unpack by simp
                 show ?thesis
                    using a b c x PU.inv' by simp
               qed
               also have "... = RTS.Map (F\<^sub>a a c) (RTS.Map (Comp a b c) x)"
                 using a b c x Map_F\<^sub>a_simp R''.HOM_null_char RTS.bij_mkarr(3)
                       UP_DN.G.extensional arr_char ide_F\<^sub>o
                 by force
               also have "... = (RTS.Map (F\<^sub>a a c) \<circ> RTS.Map (Comp a b c)) x"
                 by simp
               also have "... = RTS.Map (F\<^sub>a a c \<cdot> Comp a b c) x"
                 using a b c x F\<^sub>a_in_hom [of a c] Comp_in_hom [of a b c]
                       RTS.Map_comp by fastforce
               finally show ?thesis by blast
             qed
           qed
         qed
       qed
     qed

     lemma induces_rts_enriched_functor:
     shows "rts_enriched_functor
              Obj Hom Id Comp R''.Obj R''.Hom R''.Id R''.Comp F\<^sub>o F\<^sub>a"
       ..

     proposition induces_fully_faithful_rts_enriched_functor:
     shows "fully_faithful_rts_enriched_functor
              Obj Hom Id Comp R''.Obj R''.Hom R''.Id R''.Comp F\<^sub>o F\<^sub>a"
     proof
       show "\<And>a b. \<lbrakk>a \<in> Obj; b \<in> Obj\<rbrakk> \<Longrightarrow> RTS.iso (F\<^sub>a a b)"
       proof -
         fix a b
         assume a: "a \<in> Obj" and b: "b \<in> Obj"
         (* TODO: Figure out how to avoid or generalize this frequently occuring fact. *)
         have *: "R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b) =
                  sub_rts.resid R' (\<lambda>t. H'.in_hom t (F\<^sub>o a) (F\<^sub>o b))"
           using a b R''.Hom_def [of "F\<^sub>o a" "F\<^sub>o b"] ide_F\<^sub>o RTS.bij_mkide(3) by auto
         show "RTS.iso (F\<^sub>a a b)"
         proof -
           have "invertible_simulation
                   (RTS.Rts (RTS.dom (F\<^sub>a a b))) (RTS.Rts (RTS.cod (F\<^sub>a a b)))
                   (RTS.Map (F\<^sub>a a b))"
           proof (unfold invertible_simulation_iff, intro conjI)
             interpret F\<^sub>a_ab: simulation
                                \<open>RTS.Rts (RTS.dom (F\<^sub>a a b))\<close>
                                \<open>RTS.Rts (RTS.cod (F\<^sub>a a b))\<close>
                                \<open>RTS.Map (F\<^sub>a a b)\<close>
               using a b F\<^sub>a_in_hom RTS.arrD by blast
             show "simulation
                     (RTS.Rts (RTS.dom (F\<^sub>a a b))) (RTS.Rts (RTS.cod (F\<^sub>a a b)))
                     (RTS.Map (F\<^sub>a a b))"
               using F\<^sub>a_ab.simulation_axioms by simp
             show "bij_betw (RTS.Map (F\<^sub>a a b))
                     (Collect (residuation.arr (RTS.Rts (RTS.dom (F\<^sub>a a b)))))
                     (Collect (residuation.arr (RTS.Rts (RTS.cod (F\<^sub>a a b)))))"
             proof (intro bij_betwI)
               have Dom: "RTS.Rts (RTS.dom (F\<^sub>a a b)) = HOM\<^sub>E\<^sub>C a b"
                 using a b F\<^sub>a_in_hom [of a b] by auto
               have Cod: "RTS.Rts (RTS.cod (F\<^sub>a a b)) = R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)"
                 using a b F\<^sub>a_in_hom [of a b] by auto
               interpret DOM'_alt: sub_rts R' \<open>\<lambda>t. H'.in_hom t (F\<^sub>o a) (F\<^sub>o b)\<close>
                 using a b ide_F\<^sub>o R''.sub_rts_HOM by metis
               have Map: "RTS.Map (F\<^sub>a a b) =
                          (\<lambda>t. if residuation.arr (HOM\<^sub>E\<^sub>C a b) t
                               then DN (MkArr a b t)
                               else ResiduatedTransitionSystem.partial_magma.null
                                      (R''.HOM\<^sub>E\<^sub>C (F\<^sub>o a) (F\<^sub>o b)))"
                 using RTS.bij_mkarr(3) a b ide_F\<^sub>o by auto
               show "RTS.Map (F\<^sub>a a b) \<in> Collect F\<^sub>a_ab.A.arr \<rightarrow> Collect F\<^sub>a_ab.B.arr"
                 using F\<^sub>a_ab.preserves_reflects_arr by blast
               let ?g = "\<lambda>t. if F\<^sub>a_ab.B.arr t then Trn (UP t) else F\<^sub>a_ab.A.null"
               show g_mapsto: "?g \<in> Collect F\<^sub>a_ab.B.arr \<rightarrow> Collect F\<^sub>a_ab.A.arr"
               proof
                 fix t
                 assume t: "t \<in> Collect F\<^sub>a_ab.B.arr"
                 have gt: "?g t = Trn (UP t)"
                   using t by simp
                 have "arr (UP t)"
                   using a b t Cod UP_DN.F.preserves_reflects_arr
                         R''.HOM_arr_char ide_F\<^sub>o
                   by fastforce
                 moreover have "Dom (UP t) = a"
                 proof -
                   have 1: "DOM'_alt.arr t"
                     using t * Cod by auto
                   have "Dom (UP t) = Dom (H.dom (UP t))"
                     using t
                     by (simp add: H_dom_char UP_DN.F.extensional)
                   also have "... = Dom (UP (H'.dom t))"
                     using t 1 H'_dom_char UP_DN.inv'_simp [of "H.dom (UP t)"]
                           DOM'_alt.arr_char DOM'_alt.inclusion
                     by auto
                   also have "... = Dom (UP (F\<^sub>o a))"
                     using 1 DOM'_alt.arr_char by auto
                   also have "... = a"
                     using a Id_yields_horiz_ide
                     by (simp add: H_ide_char horizontal_unit_def)
                   finally show ?thesis by blast
                 qed
                 moreover have "Cod (UP t) = b"
                 proof -
                   have 1: "DOM'_alt.arr t"
                     using t * Cod by auto
                   have "Cod (UP t) = Cod (H.cod (UP t))"
                     using t H_cod_char
                     by (metis (no_types, lifting) Cod.simps(1) cod.extensional
                         H_cod_simp UP_DN.F.extensional UP_DN.F.preserves_reflects_arr)
                   also have "... = Cod (UP (H'.cod t))"
                     using t 1 H'_cod_char UP_DN.inv'_simp
                           DOM'_alt.arr_char DOM'_alt.inclusion
                     by auto
                   also have "... = Cod (UP (F\<^sub>o b))"
                     using 1 DOM'_alt.arr_char by auto
                   also have "... = b"
                     using b Id_yields_horiz_ide
                     by (simp add: H_ide_char horizontal_unit_def)
                   finally show ?thesis by blast
                 qed
                 ultimately have "residuation.arr (HOM\<^sub>E\<^sub>C a b) (Trn (UP t))"
                   using arr_char by blast
                 thus "?g t \<in> Collect F\<^sub>a_ab.A.arr"
                   using gt Dom by simp
               qed
               show "\<And>x. x \<in> Collect F\<^sub>a_ab.A.arr \<Longrightarrow> ?g (RTS.Map (F\<^sub>a a b) x) = x"
               proof -
                 fix x
                 assume x: "x \<in> Collect F\<^sub>a_ab.A.arr"
                 have "?g (RTS.Map (F\<^sub>a a b) x) = Trn (UP (DN (MkArr a b x)))"
                   using a b x F\<^sub>a_ab.preserves_reflects_arr RTS.Map_mkarr
                   apply auto[1]
                   using Dom Map by force
                 also have "... = x"
                   using Dom a b x arr_MkArr by auto
                 finally show "?g (RTS.Map (F\<^sub>a a b) x) = x" by blast
               qed
               show "\<And>y. y \<in> Collect F\<^sub>a_ab.B.arr \<Longrightarrow> RTS.Map (F\<^sub>a a b) (?g y) = y"
               proof -
                 fix y
                 assume y: "y \<in> Collect F\<^sub>a_ab.B.arr"
                 have "RTS.Map (F\<^sub>a a b) (?g y) = DN (MkArr a b (Trn (UP y)))"
                   using a b y * DOM'_alt.null_char Map
                         UP_DN.G.extensional arr_char
                   by auto
                 also have "... = y"
                 proof -
                   have "arr (UP y)"
                     using Cod R''.HOM_arr_char a b ide_F\<^sub>o y by fastforce
                   moreover have "Dom (UP y) = a"
                   proof -
                     have 1: "DOM'_alt.arr y"
                       using y * Cod by auto
                     have "Dom (UP y) = Dom (H.dom (UP y))"
                       using y
                       by (simp add: H_dom_char UP_DN.F.extensional)
                     also have "... = Dom (UP (H'.dom y))"
                       using y H'_dom_char UP_DN.inv'_simp
                       apply auto[1]
                       using 1 DOM'_alt.arr_char DOM'_alt.inclusion by force
                     also have "... = Dom (UP (F\<^sub>o a))"
                       using 1 DOM'_alt.arr_char by auto
                     also have "... = a"
                       using a Id_yields_horiz_ide
                       by (simp add: H_ide_char horizontal_unit_def)
                     finally show ?thesis by blast
                   qed
                   moreover have "Cod (UP y) = b"
                   proof -
                     have 1: "DOM'_alt.arr y"
                       using y * Cod by auto
                     have "Cod (UP y) = Cod (H.cod (UP y))"
                       using y H_cod_char
                       by (metis (no_types, lifting) Cod.simps(1) cod.extensional
                           H_cod_simp UP_DN.F.extensional UP_DN.F.preserves_reflects_arr)
                     also have "... = Cod (UP (H'.cod y))"
                       using y H'_cod_char UP_DN.inv'_simp
                       apply auto[1]
                       using 1 DOM'_alt.arr_char DOM'_alt.inclusion by simp
                     also have "... = Cod (UP (F\<^sub>o b))"
                       using 1 DOM'_alt.arr_char by auto
                     also have "... = b"
                       using b Id_yields_horiz_ide
                       by (simp add: H_ide_char horizontal_unit_def)
                     finally show ?thesis by blast
                   qed
                   ultimately show ?thesis
                     using a b y MkArr_Trn [of "UP y"] by simp
                 qed
                 finally show "RTS.Map (F\<^sub>a a b) (?g y) = y" by blast
               qed
             qed
             show "\<forall>t u. F\<^sub>a_ab.B.con (RTS.Map (F\<^sub>a a b) t) (RTS.Map (F\<^sub>a a b) u)
                            \<longrightarrow> F\<^sub>a_ab.A.con t u"
             proof (intro allI impI)
               fix t u
               assume tu: "F\<^sub>a_ab.B.con (RTS.Map (F\<^sub>a a b) t) (RTS.Map (F\<^sub>a a b) u)"
               have "R'.con (DN (MkArr a b t)) (DN (MkArr a b u))"
               proof -
                 have "F\<^sub>a_ab.B.con (DN (MkArr a b t)) (DN (MkArr a b u))"
                 proof -
                   have "RTS.Map (F\<^sub>a a b) t = DN (MkArr a b t)"
                     using a b R''.HOM_null_char RTS.bij_mkarr(3) UP_DN.G.extensional
                           arr_char ide_F\<^sub>o
                     by force
                   moreover have "RTS.Map (F\<^sub>a a b) u = DN (MkArr a b u)"
                     using a b R''.HOM_null_char RTS.bij_mkarr(3) UP_DN.G.extensional
                           arr_char ide_F\<^sub>o
                     by force
                   ultimately show ?thesis
                     using tu by simp
                 qed
                 moreover have "residuation.con (R''.HOM (F\<^sub>o a) (F\<^sub>o b)) =
                                F\<^sub>a_ab.B.con"
                   using a b ide_F\<^sub>o F\<^sub>a_in_hom [of a b] R''.Hom_def RTS.bij_mkide(3)
                   by auto
                 ultimately show ?thesis
                   using a b ide_F\<^sub>o R''.sub_rts_HOM
                         sub_rts.con_char
                           [of R' "\<lambda>t. H'.in_hom t (F\<^sub>o a) (F\<^sub>o b)"
                               "DN (MkArr a b t)" "DN (MkArr a b u)"]
                   by auto
               qed
               hence "V.con (MkArr a b t) (MkArr a b u)"
                 using UP_DN.G.reflects_con by auto
               thus "F\<^sub>a_ab.A.con t u"
                 using a b con_char F\<^sub>a_in_hom [of a b] Con_def by auto
             qed
           qed
           thus ?thesis
             using a b F\<^sub>a_in_hom RTS.iso_char by blast
         qed
       qed
     qed

  end

section "\<open>\<^bold>R\<^bold>T\<^bold>S\<^sup>\<dagger>\<close> Determined by its Underlying Category"

  text\<open>
    In this section we show that the category \<open>\<^bold>R\<^bold>T\<^bold>S\<^sup>\<dagger>\<close> is fully determined by
    its subcategory \<open>\<^bold>R\<^bold>T\<^bold>S\<close> comprising the arrows that are identities for the residuation.
    Specifically, we show that there is an invertible RTS-functor from \<open>\<^bold>R\<^bold>T\<^bold>S\<^sup>\<dagger>\<close>
    to the RTS-category obtained from the category \<open>\<^bold>R\<^bold>T\<^bold>S\<close> regarded as a category
    enriched in itself.
  \<close>

  context rtscat
  begin

    text\<open>
      The following produces a stand-alone instance of the category \<open>\<^bold>R\<^bold>T\<^bold>S\<^sup>\<dagger>\<close>,
      independent of the current context.
      Arrows of \<open>\<^bold>R\<^bold>T\<^bold>S\<^sup>\<dagger>\<close> have type \<open>'A rtscatx.arr\<close>
      and they have the form \<open>MkArr A B F\<close>, where \<open>A\<close> and \<open>B\<close> have type \<open>'A resid\<close>
      and \<open>F\<close> has the type \<open>('A, 'A) exponential_rts.arr\<close> of an arrow of the
      exponential RTS \<open>[A, B]\<close>).
    \<close>

    interpretation RTSx: rtscatx arr_type ..

    text\<open>
      In the current locale context, \<open>comp\<close> is the composition for the ordinary
      category \<open>\<^bold>R\<^bold>T\<^bold>S\<close>.  As a cartesian closed category, this category determines
      a category enriched in itself.
    \<close>

    interpretation enriched_category comp Prod \<alpha> \<iota>
                     \<open>Collect ide\<close> exp ECMC.Id ECMC.Comp
      using extends_to_enriched_category by blast

    text\<open>
      This self-enriched category determines an RTS-category, using the general construction
      defined in @{locale rts_category_of_enriched_category}.  We will refer to this
      RTS-category as \<open>\<^bold>R\<^bold>C\<close>.
      Arrows of \<open>\<^bold>R\<^bold>C\<close> have type \<open>('A rtscatx.arr, 'A) RC.arr\<close> and they have the form
      \<open>RC.MkArr a b t\<close>, where \<open>a\<close> and \<open>b\<close> are objects of \<open>\<^bold>R\<^bold>T\<^bold>S\<close> and \<open>t\<close> is an arrow of the
      hom-RTS \<open>HOM\<^sub>E\<^sub>C a b\<close>, which has arrow type \<open>'A\<close>.
    \<close>

    interpretation RC: rts_category_of_enriched_category
                         arr_type \<open>Collect ide\<close> exp ECMC.Id ECMC.Comp
      ..

    text\<open>
      We now define the mapping \<open>\<Phi>\<close> which we will show to be an RTS-category isomorphism
      from \<open>\<^bold>R\<^bold>C\<close> to \<open>\<^bold>R\<^bold>T\<^bold>S\<close>.  In order to map an arrow \<open>MkArr a b t\<close> of \<open>\<^bold>R\<^bold>C\<close> to an arrow of \<open>\<^bold>R\<^bold>T\<^bold>S\<close>,
      it is necessary to use the invertible simulation \<open>RTS.Func a b\<close> to lift the arrow
      \<open>t :: 'A\<close> of \<open>HOM\<^sub>E\<^sub>C a b\<close> to an arrow \<open>RTS.Func a b t :: ('A, 'A) exponential_rts.arr\<close>
      of the exponential RTS \<open>[RTSx.Rts a, RTSx.Rts b]\<close>.
    \<close>

    definition \<Phi> :: "('A rtscatx.arr, 'A) RC.arr \<Rightarrow> 'A rtscatx.arr"
    where "\<Phi> t \<equiv> if RC.arr t
                  then RTSx.MkArr
                         (RTSx.Dom (RC.Dom t)) (RTSx.Dom (RC.Cod t))
                         (Func (RC.Dom t) (RC.Cod t) (RC.Trn t))
                  else RTSx.null"

    lemma \<Phi>_simps [simp]:
    assumes "RC.arr t"
    shows "RTSx.arr (\<Phi> t)"
    and "RTSx.dom (\<Phi> t) = RTSx.mkobj (RTSx.Dom (RC.Dom t))"
    and "RTSx.cod (\<Phi> t) = RTSx.mkobj (RTSx.Dom (RC.Cod t))"
    proof -
      show 1: "RTSx.arr (\<Phi> t)"
        unfolding \<Phi>_def Rts_def
        using assms RTSx.null_char RC.arr_char simulation_Func
              Rts_def Func_def ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C
        apply (intro RTSx.arrI)
           apply auto[3]
        apply simp
        by (metis Rts_def simulation.preserves_reflects_arr)
      show "RTSx.dom (\<Phi> t) = RTSx.mkobj (RTSx.Dom (RC.Dom t))"
        using assms 1 \<Phi>_def RC.arr_char RTSx.dom_char by simp
      show "RTSx.cod (\<Phi> t) = RTSx.mkobj (RTSx.Dom (RC.Cod t))"
        using assms 1 \<Phi>_def RC.arr_char RTSx.cod_char by simp
    qed

    lemma \<Phi>_in_hom [intro]:
    assumes "RC.arr t"
    shows "RTSx.H.in_hom (\<Phi> t)
             (RTSx.mkobj
                (RTSx.Dom (RC.Dom t))) (RTSx.mkobj (RTSx.Dom (RC.Cod t)))"
      using assms by auto

    interpretation \<Phi>: simulation RC.resid RTSx.resid \<Phi>
    proof
      show "\<And>t. \<not> RC.arr t \<Longrightarrow> \<Phi> t = RTSx.null"
        using \<Phi>_def by auto
      fix t u
      assume tu: "RC.V.con t u"
      have t: "RC.arr t" and u: "RC.arr u"
        using tu RC.V.con_implies_arr by auto
      have 0: "RC.Dom t = RC.Dom u \<and> RC.Cod t = RC.Cod u"
        using RC.con_implies_Par(1-2) tu by blast
      interpret Func: simulation \<open>RC.HOM\<^sub>E\<^sub>C (RC.Dom t) (RC.Cod t)\<close>
                        \<open>exponential_rts.resid
                           (RTSx.Dom (RC.Dom t)) (RTSx.Dom (RC.Cod t))\<close>
                        \<open>Func (RC.Dom t) (RC.Cod t)\<close>
        using t simulation_Func RC.arr_char
        by (simp add: Rts_def Func_def)
      show 1: "RTSx.V.con (\<Phi> t) (\<Phi> u)"
        using tu RTSx.con_char RC.V.con_implies_arr RTSx.arr_char \<Phi>_simps(1)
              RC.con_implies_Par \<Phi>_def
        apply auto[1]
         apply metis
        by (metis Func.preserves_con RC.Con_def RC.con_char)
      show "\<Phi> (RC.resid t u) = RTSx.resid (\<Phi> t) (\<Phi> u)"
        using t u tu 1 \<Phi>_def
        apply simp
        apply (intro conjI)
                 apply (metis (no_types, lifting) Func.preserves_resid
            RC.ConE RC.con_char)
        using RTSx.con_char by auto
    qed

    text\<open>
      The following fact is key to showing that \<open>\<Phi>\<close> is functorial.
    \<close>

    lemma Func_Trn_obj:
    assumes "RC.obj a"
    shows "Func (RC.Dom a) (RC.Cod a) (RC.Trn a) =
           exponential_rts.MkIde (I (Rts (RC.Dom a)))"
    proof -
      have a: "ide (RC.Dom a)"
        using assms RC.H.ideD(1) RC.H_arr_char by auto

      interpret Dom: extensional_rts \<open>RTSx.Dom (RC.Dom a)\<close>
        using assms Rts_def ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C(1) RC.H.ideD(1) RC.H_arr_char by simp
      interpret I_Dom: identity_simulation \<open>RTSx.Dom (RC.Dom a)\<close> ..
      interpret Exp0: exponential_rts
                        \<open>RTSx.Dom (RC.Dom a)\<close> \<open>RTSx.Dom (RC.Dom a)\<close>
        ..
      interpret DOM: extensional_rts \<open>RC.HOM\<^sub>E\<^sub>C (RC.Dom a) (RC.Dom a)\<close>
        using assms
        by (simp add: RC.H_ide_char RC.arr_char RC.horizontal_unit_def)
      have "RC.Trn a = RC.Trn (RC.mkobj (RC.Dom a))"
        using assms RC.H.ide_char [of a] RC.arr_char [of a] RC.H_dom_char
        by force
      also have "... = Exp0.Map (RTSx.Trn (ECMC.Id (RC.Dom a))) One.the_arr"
      proof -
        have "RC.mkobj (RC.Dom a) =
              RC.MkArr (RC.Dom a) (RC.Dom a)
                (RTSx.Map (ECMC.Id (RC.Dom a)) One.the_arr)"
          using Map_def by argo
        thus ?thesis by simp
      qed
      also have "... = Exp0.Map
                         (RTSx.Trn
                            (curry CMC.unity (RC.Dom a) (RC.Dom a)
                               (CMC.lunit (RC.Dom a))))
                         One.the_arr"
        using ECMC.Id_def by (simp add: curry_def)
      also have "... = (Unfunc (RC.Dom a) (RC.Dom a) \<circ>
                          Currying.Curry
                            (Cod \<iota>) (RTSx.Dom (RC.Dom a))
                              (RTSx.Dom (RC.Dom a))
                            (RTSx.Src (CMC.lunit (RC.Dom a)) \<circ>
                               Pack CMC.unity (RC.Dom a))
                            (RTSx.Trg (CMC.lunit (RC.Dom a)) \<circ>
                               Pack CMC.unity (RC.Dom a))
                            (RTSx.Map (CMC.lunit (RC.Dom a)) \<circ>
                               Pack CMC.unity (RC.Dom a)))
                            One.the_arr"
        using CMC.ide_unity ECMC.Id_def Pack_def RTSx.Map_curry Rts_def
              Unfunc_def a ide_iff_RTS_obj local.curry_def
        by force
      also have "... = (Unfunc (RC.Dom a) (RC.Dom a) \<circ>
                          Currying.Curry3
                            (Cod \<iota>) (RTSx.Dom (RC.Dom a))
                              (RTSx.Dom (RC.Dom a))
                            (product_rts.P\<^sub>0
                               (RTSx.Dom RTSx.one) (RTSx.Dom (RC.Dom a))))
                            One.the_arr"
      proof -
        have "RTSx.Map (CMC.lunit (RC.Dom a)) \<circ>
                Pack CMC.unity (RC.Dom a) =
              product_rts.P\<^sub>0 (RTSx.Dom RTSx.one) (RTSx.Dom (RC.Dom a))"
        proof -
          have "RTSx.Map (CMC.lunit (RC.Dom a)) \<circ>
                  RTSx.Pack CMC.unity (RC.Dom a) =
                RTSx.Map (CMC.pr\<^sub>0 RTSx.one (RC.Dom a)) \<circ>
                  RTSx.Pack CMC.unity (RC.Dom a)"
            using assms CMC.lunit_eq RC.H.ide_char RC.H_arr_char unity_agreement
            by (metis (no_types, lifting) mem_Collect_eq one_def)
          also have "... =  product_rts.P\<^sub>0
                              (RTSx.Dom RTSx.one) (RTSx.Dom (RC.Dom a)) \<circ>
                             (Unpack RTSx.one (RC.Dom a) \<circ>
                                Pack CMC.unity (RC.Dom a))"
            using assms RTSx.Map_p\<^sub>0 RC.H.ideD(1) RC.H_arr_char pr_agreement(1)
                  ide_iff_RTS_obj
            by (auto simp add: one_def p\<^sub>0_def Pack_def Unpack_def)
          also have "... = product_rts.P\<^sub>0
                             (RTSx.Dom RTSx.one) (RTSx.Dom (RC.Dom a)) \<circ>
                             I (product_rts.resid
                                  (RTSx.Dom (RTSx.one)) (RTSx.Dom (RC.Dom a)))"
            using assms a one_def RTSx.obj_one ide_iff_RTS_obj ide_one
                  RTSx.Unpack_o_Pack
            by (auto simp add: one_def Pack_def Unpack_def)
          also have "... = product_rts.P\<^sub>0
                             (RTSx.Dom RTSx.one) (RTSx.Dom (RC.Dom a))"
            using assms one_def
                  comp_simulation_identity
                    [of "product_rts.resid
                           (RTSx.Dom (RTSx.one)) (RTSx.Dom (RC.Dom a))"
                        "RTSx.Dom (RC.Dom a)"
                        "product_rts.P\<^sub>0 (RTSx.Dom RTSx.one)
                           (RTSx.Dom (RC.Dom a))"]
            by (metis (no_types, lifting) Dom.rts_axioms Rts_def extensional_rts_def
                ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C ide_one product_rts.P\<^sub>0_is_simulation product_rts.intro)
          finally show ?thesis
            unfolding Pack_def by blast
        qed
        moreover have 1: "RTSx.sta (CMC.lunit (RC.Dom a))"
          using assms CMC.arr_lunit RC.H.ideD(1) RC.H_arr_char arr_iff_RTS_sta
          by force
        moreover have "RTSx.Src (CMC.lunit (RC.Dom a)) =
                 RTSx.Map (CMC.lunit (RC.Dom a))"
          using assms 1 RTSx.src_char RTSx.sta_char RTSx.Map_simps(3) RTSx.V.src_ide
          by (metis (no_types, lifting))
        moreover have "RTSx.Trg (CMC.lunit (RC.Dom a)) =
                 RTSx.Map (CMC.lunit (RC.Dom a))"
          using assms 1 RTSx.trg_char RTSx.sta_char RTSx.Map_simps(4) RTSx.V.trg_ide
          by (metis (no_types, lifting))
        ultimately show ?thesis
          by force
      qed
      also have "... = RTSx.Unfunc (RC.Dom a) (RC.Dom a)
                         (Exp0.MkIde (I (RTSx.Dom (RC.Dom a))))"
      proof -
        interpret Cod_\<iota>: extensional_rts \<open>Cod \<iota>\<close>
          using CMC.ide_unity extensional_rts_def by simp
        interpret C: Currying
                       \<open>Cod \<iota>\<close> \<open>RTSx.Dom (RC.Dom a)\<close> \<open>RTSx.Dom (RC.Dom a)\<close>
          ..
        have "Currying.Curry3
                (Cod \<iota>) (RTSx.Dom (RC.Dom a)) (RTSx.Dom (RC.Dom a))
                (product_rts.P\<^sub>0 (RTSx.Dom RTSx.one) (RTSx.Dom (RC.Dom a)))
                One.the_arr =
              Exp0.MkIde (I (RTSx.Dom (RC.Dom a)))"
        proof -
          interpret P: product_rts \<open>RTSx.Dom one\<close> \<open>RTSx.Dom (RC.Dom a)\<close>
            using C.AxB.product_rts_axioms Rts_def unity_agreement by argo
          have 1: "Cod_\<iota>.arr = One.arr \<and> Cod_\<iota>.src = One.src \<and> Cod_\<iota>.trg = One.trg"
            by (simp add: unity_agreement)
          have "Cod_\<iota>.arr One.the_arr"
            by (simp add: One.arr_char unity_agreement)
          moreover have "(\<lambda>g. P.P\<^sub>0 (One.the_arr, g)) = I_Dom.map"
            using P.P\<^sub>0_def One.arr_char P.arr_char Rts_def Rts_one by auto
          ultimately show ?thesis
            using 1 One.src_char One.trg_char C.Curry_def
            by (auto simp add: one_def)
        qed
        thus ?thesis
          unfolding Unfunc_def
          using One.arr_char by auto
      qed
      finally
      have "RC.Trn a =
            RTSx.Unfunc (RC.Dom a) (RC.Dom a) (Exp0.MkIde I_Dom.map)"
        by blast
      thus ?thesis
        unfolding Rts_def
        using assms RTSx.Func_Unfunc Unfunc_def Exp0.ide_MkIde
              Exp0.ide_implies_arr I_Dom.simulation_axioms RC.H_ide_char
              RC.horizontal_unit_def a ide_iff_RTS_obj Func_def
        by auto
    qed

    lemma obj_\<Phi>_obj:
    assumes "RC.obj a"
    shows "RTSx.obj (\<Phi> a)"
    proof -
      interpret Dom: extensional_rts \<open>RTSx.Dom (RC.Dom a)\<close>
        using assms RC.H.ideD(1) RC.H_arr_char Rts_def ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C by force
      interpret I_Dom: identity_simulation \<open>RTSx.Dom (RC.Dom a)\<close> ..
      interpret Exp0: exponential_rts
                        \<open>RTSx.Dom (RC.Dom a)\<close> \<open>RTSx.Dom (RC.Dom a)\<close> ..
      show ?thesis 
        unfolding \<Phi>_def
        using assms RC.H.ideD(1) Func_Trn_obj RTSx.mkobj_def Rts_def
              RTSx.obj_mkobj [of "RTSx.Dom (RC.Dom a)"]
        apply auto[1]
        by (metis (no_types, lifting) CollectD RC.H.ideD(1) RC.H_arr_char
            RC.H_ide_char RC.horizontal_unit_def Rts_def ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C)
    qed

    interpretation \<Phi>: "functor" RC.hcomp RTSx.hcomp \<Phi>
    proof
      fix f
      let ?a = "RC.Dom f"
      let ?b = "RC.Cod f"
      let ?A = "RTSx.Dom ?a"
      let ?B = "RTSx.Dom ?b"
      let ?ab = "RTSx.exp ?a ?b"
      show "\<not> RC.H.arr f \<Longrightarrow> \<Phi> f = RTSx.H.null"
        using \<Phi>_def by force
      show "RC.H.arr f \<Longrightarrow> RTSx.H.arr (\<Phi> f)"
        using RC.arr_coincidence RTSx.arr_coincidence \<Phi>.preserves_reflects_arr
        by force
      show "RC.H.arr f \<Longrightarrow> RTSx.dom (\<Phi> f) = \<Phi> (RC.dom f)"
      proof -
        assume f: "RC.H.arr f"
        have 1: "RC.Dom (RC.dom f) = ?a"
          using f RC.H.ide_dom RC.H_dom_char by simp
        have 2: "RC.Cod (RC.dom f) = ?a"
          using f RC.H.ide_dom RC.H_dom_char by simp
        have 3: "RTSx.dom (\<Phi> f) = RTSx.mkobj ?A"
          using f by simp
        have "\<Phi> (RC.dom f) = RTSx.mkobj ?A"
        proof -
          have "\<Phi> (RC.dom f) =
                RTSx.MkArr
                  (RTSx.Dom (RC.Dom (RC.dom f)))
                  (RTSx.Dom (RC.Cod (RC.dom f)))
                  (RTSx.Func (RC.Dom (RC.dom f)) (RC.Cod (RC.dom f))
                     (RC.Trn (RC.dom f)))"
            unfolding \<Phi>_def Func_def
            using f by simp
          also have "... = RTSx.MkArr ?A ?A
                             (exponential_rts.MkArr (I ?A) (I ?A) (I ?A))"
          proof -
            have "RC.obj (RC.dom f)"
              using f by simp
            thus ?thesis
              using 1 2 Func_Trn_obj [of "RC.dom f"]
              unfolding Func_def Rts_def by presburger
          qed
          also have "... = RTSx.mkobj ?A"
            unfolding RTSx.mkobj_def
            using f by blast
          finally show ?thesis by blast
        qed
        moreover have "RTSx.dom (\<Phi> f) = RTSx.mkobj ?A"
          using f by simp
        ultimately show "RTSx.dom (\<Phi> f) = \<Phi> (RC.dom f)"
          by simp
      qed
      show "RC.H.arr f \<Longrightarrow> RTSx.cod (\<Phi> f) = \<Phi> (RC.cod f)"
      proof -
        assume f: "RC.H.arr f"
        have 1: "RC.Dom (RC.cod f) = ?b"
          using f RC.H.ide_cod RC.H_cod_char by simp
        have 2: "RC.Cod (RC.cod f) = ?b"
          using f RC.H.ide_cod RC.H_cod_char by simp
        have 3: "RTSx.cod (\<Phi> f) = RTSx.mkobj ?B"
          using f by simp
        have "\<Phi> (RC.cod f) = RTSx.mkobj ?B"
        proof -
          have "\<Phi> (RC.cod f) =
                RTSx.MkArr
                  (RTSx.Dom (RC.Dom (RC.cod f)))
                  (RTSx.Dom (RC.Cod (RC.cod f)))
                  (RTSx.Func (RC.Dom (RC.cod f)) (RC.Cod (RC.cod f))
                     (RC.Trn (RC.cod f)))"
            unfolding \<Phi>_def Func_def
            using f by simp
          also have "... = RTSx.MkArr ?B ?B
                             (exponential_rts.MkArr (I ?B) (I ?B) (I ?B))"
          proof -
            have "RC.obj (RC.cod f)"
              using f by simp
            thus ?thesis
              using 1 2 Func_Trn_obj [of "RC.cod f"]
              unfolding Func_def Rts_def by presburger
          qed
          also have "... = RTSx.mkobj ?B"
            unfolding RTSx.mkobj_def
            using f by blast
          finally show ?thesis by blast
        qed
        moreover have "RTSx.cod (\<Phi> f) = RTSx.mkobj ?B"
          using f by simp
        ultimately show "RTSx.cod (\<Phi> f) = \<Phi> (RC.cod f)"
          by simp
      qed
      fix g
      let ?c = "RC.Cod g"
      let ?C = "RTSx.Dom ?c"
      let ?bc = "RTSx.exp ?b ?c"
      let ?ac = "RTSx.exp ?a ?c"
      show "RC.H.seq g f \<Longrightarrow> \<Phi> (RC.hcomp g f) = RTSx.hcomp (\<Phi> g) (\<Phi> f)"
      proof -
        assume seq: "RC.H.seq g f"
        have 0: "RC.H.arr f \<and> RC.H.arr g \<and> RC.dom g = RC.cod f"
          using seq by blast
        interpret A: extensional_rts ?A
          using seq 0 RC.H_arr_char Rts_def ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C by fastforce
        interpret B: extensional_rts ?B
          using seq 0 RC.H_arr_char Rts_def ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C by fastforce
        interpret C: extensional_rts ?C
          using seq 0 RC.H_arr_char Rts_def ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C by fastforce
        interpret AB: exponential_rts ?A ?B ..
        interpret BC: exponential_rts ?B ?C ..
        interpret AC: exponential_rts ?A ?C ..
        interpret CMP: COMP ?A ?B ?C ..
        interpret ASC: ASSOC BC.resid AB.resid ?A ..
        interpret HOM_ab: extensional_rts \<open>RC.HOM\<^sub>E\<^sub>C ?a ?b\<close>
          by (meson RC.H_seq_char RC.rts_category_of_enriched_category_axioms
              ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C(1) ide_Hom rts_category_of_enriched_category.arr_char seq)
        interpret HOM_bc: extensional_rts \<open>RC.HOM\<^sub>E\<^sub>C ?b ?c\<close>
          by (meson RC.H_seq_char RC.rts_category_of_enriched_category_axioms
              ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C(1) ide_Hom rts_category_of_enriched_category.arr_char seq)
        interpret HOM_ac: extensional_rts \<open>RC.HOM\<^sub>E\<^sub>C ?a ?c\<close>
          by (meson RC.H_seq_char RC.rts_category_of_enriched_category_axioms
              ideD\<^sub>R\<^sub>T\<^sub>S\<^sub>C(1) ide_Hom rts_category_of_enriched_category.arr_char seq)
        let ?Func_ab = "RTSx.Func ?a ?b"
        let ?Func_bc = "RTSx.Func ?b ?c"
        let ?Func_ac = "RTSx.Func ?a ?c"
        interpret Func_ab: simulation \<open>RC.HOM\<^sub>E\<^sub>C ?a ?b\<close> AB.resid ?Func_ab
          using 0 simulation_Func
          by (metis (no_types, lifting) RC.H_arr_char Rts_def Func_def mem_Collect_eq)
        interpret Func_ab: simulation_between_extensional_rts
                             \<open>RC.HOM\<^sub>E\<^sub>C ?a ?b\<close> AB.resid ?Func_ab
          ..
        interpret Func_bc: simulation \<open>RC.HOM\<^sub>E\<^sub>C ?b ?c\<close> BC.resid ?Func_bc
          using 0 simulation_Func
          by (metis (no_types, lifting) RC.H_arr_char Rts_def Func_def mem_Collect_eq)
        interpret Func_bc: simulation_between_extensional_rts
                             \<open>RC.HOM\<^sub>E\<^sub>C ?b ?c\<close> BC.resid ?Func_bc
          ..
        interpret Func_ac: simulation \<open>RC.HOM\<^sub>E\<^sub>C ?a ?c\<close> AC.resid ?Func_ac
          using 0 simulation_Func
          by (metis (no_types, lifting) RC.H_arr_char Rts_def Func_def mem_Collect_eq)
        interpret Func_ac: simulation_between_extensional_rts
                             \<open>RC.HOM\<^sub>E\<^sub>C ?a ?c\<close> AC.resid ?Func_ac
          ..
        interpret Comp: Composition arr_type ?a ?b ?c
          using seq RC.arr_char RC.H_seq_char 
          by unfold_locales auto
        interpret bcXab: product_rts \<open>Comp.EXP ?b ?c\<close> \<open>Comp.EXP ?a ?b\<close> ..
        interpret Func_bc_x_Func_ab:
                    product_simulation \<open>Comp.EXP ?b ?c\<close> \<open>Comp.EXP ?a ?b\<close>
                      BC.resid AB.resid \<open>RTSx.Func ?b ?c\<close> \<open>RTSx.Func ?a ?b\<close>
          ..
        interpret Eval_BC: RTSConstructions.evaluation_map ?B ?C ..
        interpret Eval_AB: RTSConstructions.evaluation_map ?A ?B ..
        interpret I_BC: identity_simulation BC.resid ..
        interpret I_BC_x_Eval_AB: product_simulation
                                    BC.resid ASC.BxC.resid BC.resid ?B
                                    I_BC.map Eval_AB.map
          ..
        have 0: "bcXab.arr (RC.Trn g, RC.Trn f)"
          using seq bcXab.arr_char RC.H.seqE RC.H_arr_char RC.H_seq_char
          by auto
        have 1: "CMP.BCxAB.arr
                   (RTSx.Func ?b ?c (RC.Trn g), RTSx.Func ?a ?b (RC.Trn f))"
          using 0 by auto
        have "\<Phi> (RC.hcomp g f) =
              RTSx.MkArr
                (RTSx.Dom (RC.Dom (RC.hcomp g f)))
                (RTSx.Dom (RC.Cod (RC.hcomp g f)))
                (RTSx.Func (RC.Dom (RC.hcomp g f)) (RC.Cod (RC.hcomp g f))
                   (RC.Trn (RC.hcomp g f)))"
          using seq \<Phi>_def by (auto simp add: Func_def)
        also have "... =                                  
                   RTSx.MkArr ?A ?C
                     ((?Func_ac \<circ> AC.Map (RTSx.Trn (ECMC.Comp ?a ?b ?c)))
                         (RTSx.Pack ?bc ?ab (RC.Trn g, RC.Trn f)))"
          unfolding RC.hcomp_def
          using seq RC.H_seq_char
          by (auto simp add: Func_def Pack_def Map_def exp_def)
        also have "... =
                   RTSx.MkArr ?A ?C
                     (CMP.map
                        (Func_bc_x_Func_ab.map
                           (RTSx.Unpack ?bc ?ab
                              (RTSx.Pack ?bc ?ab (RC.Trn g, RC.Trn f)))))"
          using Comp.Func_o_Map_Comp
          by (auto simp add: Func_def Unpack_def Map_def exp_def Rts_def)
        also have "... =
                   RTSx.MkArr ?A ?C
                     (CMP.map
                        (Func_bc_x_Func_ab.map
                           (RC.Trn g, RC.Trn f)))"
          using RC.H_seq_char RC.arr_char ide_Hom seq RTSx.Unpack_Pack
          by (metis (no_types, lifting) 0 Rts_def exp_def ide_iff_RTS_obj)
        also have "... =
                   RTSx.MkArr ?A ?C
                     (CMP.map
                        (RTSx.Func ?b ?c (RC.Trn g), RTSx.Func ?a ?b (RC.Trn f)))"
          using 0 Func_bc_x_Func_ab.map_simp by fastforce
        also have "... =
                   RTSx.MkArr ?A ?C
                     (CMP.Currying.A_BC.MkArr
                        (BC.Dom (RTSx.Func ?b ?c (RC.Trn g)) \<circ>
                           BC.Dom (RTSx.Func ?a ?b (RC.Trn f)))
                        (BC.Cod (RTSx.Func ?b ?c (RC.Trn g)) \<circ>
                           BC.Cod (RTSx.Func ?a ?b (RC.Trn f)))
                        (BC.Map (RTSx.Func ?b ?c (RC.Trn g)) \<circ>
                           BC.Map (RTSx.Func ?a ?b (RC.Trn f))))"
          unfolding CMP.Currying.Curry_def
          using 0 CMP.map_eq by simp
        also have "... =
                   RTSx.MkArr ?A ?C
                     (COMP.map ?A ?B ?C
                        (RTSx.Func ?b ?c (RC.Trn g), RTSx.Func ?a ?b (RC.Trn f)))"
          unfolding CMP.Currying.Curry_def
          using 0 CMP.map_eq by simp
        also have "... = RTSx.hcomp (\<Phi> g) (\<Phi> f)"
          unfolding RTSx.hcomp_def
          using seq RC.H_seq_char \<Phi>_def \<Phi>_simps(1)
          apply (auto simp add: Func_def)[1]
          by (metis (no_types, lifting))
        finally show ?thesis by blast
      qed
    qed

    interpretation \<Phi>: rts_functor RC.resid RC.hcomp
                         RTSx.resid RTSx.hcomp \<Phi>
      ..

    interpretation \<Phi>: fully_faithful_functor RC.hcomp RTSx.hcomp \<Phi>
    proof
      fix t u
      assume par: "RC.H.par t u"
      assume eq: "\<Phi> t = \<Phi> u"
      show "t = u"
      proof (intro RC.arr_eqI)
        show "t \<noteq> RC.null" and "u \<noteq> RC.null"
          using par by auto
        show 1: "RC.Dom t = RC.Dom u" and 2: "RC.Cod t = RC.Cod u"
          using par eq \<Phi>_def RC.H_dom_char RC.H_cod_char by auto
        show "RC.Trn t = RC.Trn u"
        proof -
          have "RC.Trn t = RTSx.Unfunc (RC.Dom t) (RC.Cod t)
                             (RTSx.Func (RC.Dom t) (RC.Cod t) (RC.Trn t))"
            using par RTSx.Unfunc_Func RC.arr_char [of t]
            apply auto[1]
            by (simp add: Rts_def exp_def ide_iff_RTS_obj)
          also have "... = RTSx.Unfunc (RC.Dom u) (RC.Cod u)
                             (RTSx.Func (RC.Dom t) (RC.Cod t) (RC.Trn t))"
            using 1 2 by auto
          also have "... = RTSx.Unfunc (RC.Dom u) (RC.Cod u)
                             (RTSx.Func (RC.Dom u) (RC.Cod u) (RC.Trn u))"
            using par eq \<Phi>_def
            by (auto simp add: Func_def)
          also have "... = RC.Trn u"
            using par RTSx.Unfunc_Func RC.arr_char [of t] RC.arr_char [of u]
            apply auto[1]
            by (simp add: Rts_def exp_def ide_iff_RTS_obj)
          finally show "RC.Trn t = RC.Trn u" by blast
        qed
      qed
      next
      fix a b g
      assume a: "RC.obj a" and b: "RC.obj b"
      assume g: "RTSx.H.in_hom g (\<Phi> a) (\<Phi> b)"
      have 1: "RTSx.dom g = RC.Dom a"
        by (metis (no_types, lifting) CollectD RC.H.ide_char' RC.H_arr_char
            RC.H_ide_char RC.horizontal_unit_def RTSx.H.cod_dom RTSx.H.in_homE
            RTSx.bij_mkobj(4) \<Phi>_simps(3) a g ide_iff_RTS_obj)
      have 2: "RTSx.cod g = RC.Dom b"
        by (metis (no_types, lifting) CollectD RC.H_ide_char RC.arr_char
            RC.horizontal_unit_def RTSx.Dom.simps(1) RTSx.H.ide_cod RTSx.H.in_homE
            Rts_def \<Phi>_def b bij_mkide(4) g ide_iff_RTS_obj)
      interpret Dom_a: extensional_rts \<open>RTSx.Dom (RC.Dom a)\<close>
        using a \<Phi>_def RC.H.ide_char [of a] RC.arr_char [of a] obj_\<Phi>_obj
        by force
      interpret Dom_b: extensional_rts \<open>RTSx.Dom (RC.Dom b)\<close>
        using b \<Phi>_def RC.H.ide_char [of b] RC.arr_char [of b] obj_\<Phi>_obj
        by force
      interpret Exp: exponential_rts
                       \<open>RTSx.Dom (RC.Dom a)\<close> \<open>RTSx.Dom (RC.Dom b)\<close>
        ..
      interpret Unfunc: simulation
                          Exp.resid \<open>RC.HOM\<^sub>E\<^sub>C (RC.Dom a) (RC.Dom b)\<close>
                          \<open>RTSx.Unfunc (RC.Dom a) (RC.Dom b)\<close>
        by (metis 1 2 RTSx.H.arrI RTSx.H.ide_cod RTSx.H.ide_dom
            RTSx.simulation_Unfunc Rts_def exp_def g)
      let ?f = "RC.MkArr (RC.Dom a) (RC.Dom b)
                  (RTSx.Unfunc (RC.Dom a) (RC.Dom b) (RTSx.Trn g))"
      have "RC.H.in_hom ?f a b \<and> \<Phi> ?f = g"
      proof
        show 3: "RC.H.in_hom ?f a b"
        proof
          show 4: "RC.H.arr ?f"
            using a b g 1 2
                  RTSx.arr_char RC.arr_char Unfunc.preserves_reflects_arr
                  RC.arr_MkArr
            by (metis (no_types, lifting) RC.H.ideD(1) RC.H_arr_char
                RTSx.Dom_cod RTSx.Dom_dom RTSx.H.in_homE RTSx.arr_coincidence\<^sub>C\<^sub>R\<^sub>C)
          show "RC.dom ?f = a"
            using 4 RC.H.ideD(1-2) RC.H_dom_char a by auto
          show "RC.cod ?f = b"
            using 4 RC.H.ideD(1-3) RC.H_dom_char RC.H_cod_char b by auto
        qed
        show "\<Phi> ?f = g"
        proof -
          have "RTSx.Func (RC.Dom a) (RC.Dom b)
                  (RTSx.Unfunc (RC.Dom a) (RC.Dom b) (RTSx.Trn g)) =
                RTSx.Trn g"
            using 1 2 RTSx.Func_Unfunc
            by (metis (no_types, lifting) RTSx.Dom_cod RTSx.Dom_dom RTSx.H.in_homE
                RTSx.arr_char RTSx.arr_coincidence\<^sub>C\<^sub>R\<^sub>C a b g obj_\<Phi>_obj)
          thus ?thesis
            unfolding \<Phi>_def
            using g 1 2 3 RTSx.arr_MkArr RTSx.arr_char [of g]
            apply (auto simp add: Func_def)[1]
            by (metis (no_types, lifting) RTSx.Dom_cod RTSx.Dom_dom RTSx.MkArr_Trn)
        qed
      qed
      thus "\<exists>f. RC.H.in_hom f a b \<and> \<Phi> f = g" by blast
    qed

    interpretation \<Phi>: full_embedding_functor RC.hcomp RTSx.hcomp \<Phi>
    proof
      fix f f'
      assume f: "RC.H.arr f" and f': "RC.H.arr f'"
      assume eq: "\<Phi> f = \<Phi> f'"
      have "RC.H.par f f'"
        using f f' eq bij_mkide(4) RC.H_cod_char RC.H_dom_char
        apply (auto simp add: \<Phi>_def Rts_def)[1]
        by (metis (no_types, lifting) CollectD RC.H_arr_char f f')+
      thus "f = f'"
        using \<Phi>.is_faithful eq by blast
    qed

    interpretation \<Phi>: invertible_functor RC.hcomp RTSx.hcomp \<Phi>
    proof -
      have "Collect RTSx.obj \<subseteq> \<Phi> ` Collect RC.obj"
      proof
        fix a
        assume a: "a \<in> Collect RTSx.obj"
        show "a \<in> \<Phi> ` Collect RC.obj"
        proof
          let ?a' = "RC.mkobj a"
          show a': "?a' \<in> Collect RC.obj"
            using a RC.Id_yields_horiz_ide ide_iff_RTS_obj by blast
          show "a = \<Phi> ?a'"
            using a a' bij_mkide(4)
            apply (auto simp add: \<Phi>_def)[1]
             apply (metis (no_types, lifting) RC.Cod.simps(1) RC.Dom.simps(1)
                RC.H.ide_char RC.Trn.simps(1) RTSx.Dom.simps(1) RTSx.bij_mkobj(4)
                RTSx.dom_char \<Phi>.as_nat_trans.preserves_dom
                \<Phi>.as_nat_trans.preserves_reflects_arr \<Phi>_def)
            by (metis (no_types, lifting) RC.H.ide_char RC.arr_coincidence)
        qed
      qed
      thus "invertible_functor RC.hcomp RTSx.hcomp \<Phi>"
        using \<Phi>.is_invertible_if_surjective_on_objects(1) by blast
    qed

    interpretation \<Phi>: invertible_simulation RC.resid RTSx.resid \<Phi>
    proof -
      have "\<And>t u. RTSx.V.con (\<Phi> t) (\<Phi> u) \<Longrightarrow> RC.V.con t u"
      proof -
        fix t u
        assume con: "RTSx.V.con (\<Phi> t) (\<Phi> u)"
        have 1: "RTSx.V.con
                   (RTSx.MkArr (RTSx.Dom (RC.Dom t)) (RTSx.Dom (RC.Cod t))
                      (RTSx.Func (RC.Dom t) (RC.Cod t) (RC.Trn t)))
                   (RTSx.MkArr (RTSx.Dom (RC.Dom u)) (RTSx.Dom (RC.Cod u))
                      (RTSx.Func (RC.Dom u) (RC.Cod u) (RC.Trn u)))"
          using con \<Phi>_def
          unfolding Func_def
          by (metis RTSx.V.not_con_null(1) RTSx.V.not_con_null(2))
        hence "residuation.con
                 (exponential_rts.resid
                    (RTSx.Dom (RC.Dom t)) (RTSx.Dom (RC.Cod t)))
                 (RTSx.Func (RC.Dom t) (RC.Cod t) (RC.Trn t))
                 (RTSx.Func (RC.Dom u) (RC.Cod u) (RC.Trn u))"
          using RTSx.con_char by force
        hence "residuation.con (RC.HOM\<^sub>E\<^sub>C (RC.Dom t) (RC.Cod t))
                 (RTSx.Unfunc (RC.Dom t) (RC.Cod t)
                    (RTSx.Func (RC.Dom t) (RC.Cod t) (RC.Trn t)))
                 (RTSx.Unfunc (RC.Dom u) (RC.Cod u)
                    (RTSx.Func (RC.Dom u) (RC.Cod u) (RC.Trn u)))"
          using con 1 simulation.preserves_con simulation_Unfunc bij_mkide(4)
          by (metis (no_types, lifting) CollectD RC.H_arr_char RTSx.Cod.simps(1)
              RTSx.Dom.simps(1) RTSx.con_char RTSx.con_implies_par Rts_def
              Unfunc_def \<Phi>.as_nat_trans.preserves_reflects_arr)
        hence "residuation.con (RC.HOM\<^sub>E\<^sub>C (RC.Dom t) (RC.Cod t)) 
                 (RC.Trn t) (RC.Trn u)"
          using RC.arr_char RTSx.con_char Unfunc_Func
          by (metis (no_types, lifting) CollectD RC.H_arr_char RTSx.con_implies_par
              Unfunc_def \<Phi>.as_nat_trans.preserves_reflects_arr con Func_def)
        thus "RC.V.con t u"
          using 1 con bij_mkide(4) RC.con_char RTSx.con_char RC.arr_char
                RTSx.con_implies_par RTSx.null_char \<Phi>.extensional Rts_def bij_mkide(4)
          apply auto[1]
          apply (intro RC.ConI conjI, auto)
          by metis+
      qed
      thus "invertible_simulation RC.resid RTSx.resid \<Phi>"
        using \<Phi>.is_invertible_simulation_if \<Phi>.invertible_functor_axioms by blast
    qed

    theorem "rts_category_isomorphism RC.resid RC.hcomp
               RTSx.resid RTSx.hcomp \<Phi>"
      ..

  end

end
