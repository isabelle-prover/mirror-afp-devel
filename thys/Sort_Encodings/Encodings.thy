section{* End Results in Locale-Free Form *}
theory Encodings
imports G T E
begin

text{* This section contains the outcome of our type-encoding results,
presented in a locale-free fashion. It is not very useful
from an Isabelle development point of view, where the locale theorems are fine.

Rather, this is aimed as a quasi-self-contained formal documentation of
the overall results for the non-Isabelle-experts. *}


subsection {* Soundness *}

text{* In the soundness theorems below, we employ the following Isabelle types:
\\- type variables (parameters):
\\--- @{text "'tp"}, of types
\\--- @{text "'fsym"}, of function symbols
\\--- @{text "'psym"}, of predicate symbols
%
\\- a fixed countable universe @{text "univ"} for the carrier of the models
%
\\
and various operators on these types:

(1) the constitutive parts of FOL signatures:
\\---- the boolean predicates
@{text "wtFsym"} and @{text "wtPsym"}, indicating the ``well-typed'' function and predicate
symbols; these are just means to select only subsets of these symbols
for consideration in the signature
\\---- the operators arOf and resOf, giving the arity and the result type
of function symbols
\\---- the operator parOf, giving the arity of predicate symbols

(2) the problem, @{text "\<Phi>"}, which is a set of clauses over the considered signature

(3) a partition of the types in:
\\--- @{text "tpD"}, the types that should be decorated in any case
\\--- @{text "tpFD"}, the types that should be decorated in a featherweight fashion
\\--- for guards only, a further refinement of @{text "tpD"}, indicating, as @{text "tpCD"},
the types that should be classically (i.e., traditionally) decorated
(these partitionings are meant to provide a uniform treatment of the
three styles of encodings:
traditional, lightweight and featherweight)

(4) the constitutive parts of a structure over the considered signature:
\\---- @{text "intT"}, the interpretation of each type as a unary predicate (essentially, a set)
over an arbitrary type 'univ
\\---- @{text "intF"} and @{text "intP"}, the interpretations of the function and predicate symbols
as actual functions and predicates over @{text "univ"}.


*}


text{* \ \\ \bf Soundness of the tag encodings: \ \\ *}

text{* The assumptions of the tag soundness theorems are the following:

(a)  @{text "ProblemIkTpart wtFsym wtPsym arOf resOf parOf \<Phi> infTp tpD tpFD"},
stating that:
\\--- @{text "(wtFsym, wtPsym, arOf, resOf, parOf)"} form a countable signature
\\--- @{text "\<Phi>"} is a well-typed problem over this signature
\\--- @{text "infTp"} is an indication of the types that the problem guarantees as infinite
in all models
\\--- @{text "tpD"} and @{text "tpFD"} are disjoint and all types that are not
 marked as @{text "tpD"} or @{text "tpFD"}
are deemed safe by the monotonicity calculus from @{text "Mcalc"}

(b) @{text "CM.Model wtFsym wtPsym arOf resOf parOf \<Phi> intT intF intP"}
says that @{text "(intT, intF, intP)"} is a model for @{text "\<Phi>"} (hence @{text "\<Phi>"} is satisfiable)

The conclusion says that we obtain a model of the untyped version of the problem
(after suitable tags and axioms have been added): *}


text{* Because of the assumptions on tpD and tpFD, we have the following particular cases
of our parameterized tag encoding:
\\-- if @{text "tpD"} is taked to be everywhere true (hence @{text "tpFD"} becomes everywhere false), we
obtain the traditional tag encoding
\\-- if @{text "tpD"} is taken to be true precisely when the monotonicity calculus fails,
we obtain the lightweight tag encoding
\\-- if @{text "tpFD"} is taken to be true precisely when the monotonicity calculus fails,
we obtain the featherweight tag encoding
*}

theorem tags_soundness:
fixes wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list" and resOf :: "'fsym \<Rightarrow> 'tp" and parOf :: "'psym \<Rightarrow> 'tp list"
and \<Phi> :: "('fsym, 'psym) prob" and infTp :: "'tp \<Rightarrow> bool"
and tpD :: "'tp \<Rightarrow> bool" and tpFD :: "'tp \<Rightarrow> bool"
and intT :: "'tp \<Rightarrow> univ \<Rightarrow> bool"
and intF :: "'fsym \<Rightarrow> univ list \<Rightarrow> univ" and intP :: "'psym \<Rightarrow> univ list \<Rightarrow> bool"
-- {* The problem translation: *}
-- {* First the addition of tags (``TE'' stands for ``tag encoding''):  *}
defines "TE_wtFsym \<equiv> ProblemIkTpart.TE_wtFsym wtFsym resOf"
and "TE_arOf \<equiv> ProblemIkTpart.TE_arOf arOf"
and "TE_resOf \<equiv> ProblemIkTpart.TE_resOf resOf"
defines "TE_\<Phi> \<equiv> ProblemIkTpart.tPB wtFsym arOf resOf \<Phi> tpD tpFD"
-- {* Then the deletion of types (``U'' stands for ``untyped''): *}
and "U_arOf \<equiv> length \<circ> TE_arOf"
and "U_parOf \<equiv> length \<circ> parOf"
defines "U_\<Phi> \<equiv> TE_\<Phi>"
-- {* The forward model translation: *}
-- {* First, using monotonicity, we build an infinite model of @{text"\<Phi>"}
  (``I'' stands for ``infinite''):  *}
defines "intTI \<equiv> MonotProblem.intTI TE_wtFsym wtPsym TE_arOf TE_resOf parOf TE_\<Phi>"
and "intFI \<equiv> MonotProblem.intFI TE_wtFsym wtPsym TE_arOf TE_resOf parOf TE_\<Phi>"
and "intPI \<equiv> MonotProblem.intPI TE_wtFsym wtPsym TE_arOf TE_resOf parOf TE_\<Phi>"
-- {* Then, by isomorphic transfer of the lattter model, we build a model of @{text"\<Phi>"}
 that has all types interpeted as @{text "univ"} (``F'' stands for ``full"): *}
defines "intFF \<equiv> InfModel.intFF TE_arOf TE_resOf intTI intFI"
and "intPF \<equiv> InfModel.intPF parOf intTI intPI"
-- {* Then we build a model of @{text "U_\<Phi>"}: *}
defines "U_intT \<equiv> InfModel.intTF (any::'tp)"

-- {* Assumptions of the theorem: *}
assumes
P: "ProblemIkTpart wtFsym wtPsym arOf resOf parOf \<Phi> infTp tpD tpFD"
and M: "CM.Model wtFsym wtPsym arOf resOf parOf \<Phi> intT intF intP"

-- {* Conclusion of the theorem: *}
shows "CU.Model TE_wtFsym wtPsym U_arOf U_parOf U_\<Phi> U_intT intFF intPF"

unfolding U_arOf_def U_parOf_def U_\<Phi>_def
unfolding U_intT_def intTI_def intFI_def intPI_def intFF_def intPF_def
apply(rule M_MonotModel.M_U_soundness)
unfolding M_MonotModel_def MonotModel_def apply safe
  unfolding TE_wtFsym_def TE_arOf_def TE_resOf_def TE_\<Phi>_def
  apply(rule ProblemIkTpart.T_monotonic)
   apply(rule P)
   apply(rule ModelIkTpart.T_soundness) unfolding ModelIkTpart_def apply safe
     apply(rule P)
     apply(rule M)
done


text{* \ \\ \bf Soundness of the guard encodings: \ \\ *}

text{* Here the assumptions and conclusion have a similar shapes as those
for the tag encodings. The difference is in the first assumption,
@{text "ProblemIkTpartG wtFsym wtPsym arOf resOf parOf \<Phi> infTp tpD tpFD tpCD"},
which consists of @{text "ProblemIkTpart wtFsym wtPsym arOf resOf parOf \<Phi> infTp tpD tpFD"} together
with the following assumptions about @{text "tpCD"}:
\\-- @{text "tpCD"} is included in @{text "tpD"}
\\-- if a result type of an operation symbol is in @{text "tpD"}, then so are all the types in its arity
*}

text{* We have the following particular cases of our parameterized guard encoding:
\\-- if @{text "tpD"} and @{text "tpCD"} are taked to be everywhere true
(hence @{text "tpFD"} becomes everywhere false),
we obtain the traditional guard encoding
\\-- if @{text "tpCD"} is taken to be false and @{text "tpD"} is taken to be true precisely when the
monotonicity calculus fails,
we obtain the lightweight tag encoding
\\-- if @{text "tpFD"} is taken to be true precisely when the monotonicity calculus fails,
we obtain the featherweight tag encoding
*}

theorem guards_soundness:
fixes wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list" and resOf :: "'fsym \<Rightarrow> 'tp" and parOf :: "'psym \<Rightarrow> 'tp list"
and \<Phi> :: "('fsym, 'psym) prob" and infTp :: "'tp \<Rightarrow> bool"
and tpD :: "'tp \<Rightarrow> bool" and tpFD :: "'tp \<Rightarrow> bool" and tpCD :: "'tp \<Rightarrow> bool"
and intT :: "'tp \<Rightarrow> univ \<Rightarrow> bool"
and intF :: "'fsym \<Rightarrow> univ list \<Rightarrow> univ"
and intP :: "'psym \<Rightarrow> univ list \<Rightarrow> bool"
-- {* The problem translation: *}
defines "GE_wtFsym \<equiv> ProblemIkTpartG.GE_wtFsym wtFsym resOf tpCD"
and "GE_wtPsym \<equiv> ProblemIkTpartG.GE_wtPsym wtPsym tpD tpFD"
and "GE_arOf \<equiv> ProblemIkTpartG.GE_arOf arOf"
and "GE_resOf \<equiv> ProblemIkTpartG.GE_resOf resOf"
and "GE_parOf \<equiv> ProblemIkTpartG.GE_parOf parOf"

defines "GE_\<Phi> \<equiv> ProblemIkTpartG.gPB wtFsym arOf resOf \<Phi> tpD tpFD tpCD"
and "U_arOf \<equiv> length \<circ> GE_arOf"
and "U_parOf \<equiv> length \<circ> GE_parOf"

defines "U_\<Phi> \<equiv> GE_\<Phi>"

-- {* The model forward translation: *}
defines "intTI \<equiv> MonotProblem.intTI GE_wtFsym GE_wtPsym GE_arOf GE_resOf GE_parOf GE_\<Phi>"
and "intFI \<equiv> MonotProblem.intFI GE_wtFsym GE_wtPsym GE_arOf GE_resOf GE_parOf GE_\<Phi>"
and "intPI \<equiv> MonotProblem.intPI GE_wtFsym GE_wtPsym GE_arOf GE_resOf GE_parOf GE_\<Phi>"

defines "intFF \<equiv> InfModel.intFF GE_arOf GE_resOf intTI intFI"
and "intPF \<equiv> InfModel.intPF GE_parOf intTI intPI"

defines "U_intT \<equiv> InfModel.intTF (any::'tp)"

assumes
P: "ProblemIkTpartG wtFsym wtPsym arOf resOf parOf \<Phi> infTp tpD tpFD tpCD"
and M: "CM.Model wtFsym wtPsym arOf resOf parOf \<Phi> intT intF intP"

shows "CU.Model GE_wtFsym GE_wtPsym U_arOf U_parOf U_\<Phi> U_intT intFF intPF"

unfolding U_arOf_def U_parOf_def U_\<Phi>_def
unfolding U_intT_def intTI_def intFI_def intPI_def intFF_def intPF_def
apply(rule M_MonotModel.M_U_soundness)
unfolding M_MonotModel_def MonotModel_def apply safe
  unfolding GE_wtFsym_def GE_wtPsym_def GE_arOf_def GE_resOf_def GE_parOf_def GE_\<Phi>_def
  apply(rule ProblemIkTpartG.G_monotonic)
   apply(rule P)
   apply(rule ModelIkTpartG.G_soundness)
   unfolding ModelIkTpartG_def ModelIkTpart_def apply safe
     apply(rule P)
     using P unfolding ProblemIkTpartG_def apply fastforce
     apply(rule M)
done


subsection {* Completeness *}

text{* The setting is similar to the one for completeness, except for the following point:

(3) The constitutive parts of a structure over the untyped signature
resulted from the addition of the tags or guards followed by
the deletion of the types: @{text "(D, eintF, eintP)"}
*}


text{* \ \\ \bf Completeness of the tag encodings \ \\ *}


theorem tags_completeness:
fixes wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list" and resOf :: "'fsym \<Rightarrow> 'tp" and parOf :: "'psym \<Rightarrow> 'tp list"
and \<Phi> :: "('fsym, 'psym) prob" and infTp :: "'tp \<Rightarrow> bool"
and tpD :: "'tp \<Rightarrow> bool" and tpFD :: "'tp \<Rightarrow> bool"

and D :: "univ \<Rightarrow> bool"
and eintF :: "('fsym,'tp) T.efsym \<Rightarrow> univ list \<Rightarrow> univ"
and eintP :: "'psym \<Rightarrow> univ list \<Rightarrow> bool"

-- {* The problem translation (the same as in the case of soundness): *}
defines "TE_wtFsym \<equiv> ProblemIkTpart.TE_wtFsym wtFsym resOf"
and "TE_arOf \<equiv> ProblemIkTpart.TE_arOf arOf"
and "TE_resOf \<equiv> ProblemIkTpart.TE_resOf resOf"
defines "TE_\<Phi> \<equiv> ProblemIkTpart.tPB wtFsym arOf resOf \<Phi> tpD tpFD"
and "U_arOf \<equiv> length \<circ> TE_arOf"
and "U_parOf \<equiv> length \<circ> parOf"
defines "U_\<Phi> \<equiv> TE_\<Phi>"

-- {* The backward model translation: *}
defines "intT \<equiv> ProblemIkTpart_TEModel.intT tpD tpFD (\<lambda>\<sigma>::'tp. D) eintF"
and "intF \<equiv> ProblemIkTpart_TEModel.intF arOf resOf tpD tpFD (\<lambda>\<sigma>::'tp. D) eintF"
and "intP \<equiv> ProblemIkTpart_TEModel.intP parOf tpD tpFD (\<lambda>\<sigma>::'tp. D) eintF eintP"

assumes
P: "ProblemIkTpart wtFsym wtPsym arOf resOf parOf \<Phi> infTp tpD tpFD" and
M: "CU.Model TE_wtFsym wtPsym (length o TE_arOf)
            (length o parOf) TE_\<Phi> D eintF eintP"

shows "CM.Model wtFsym wtPsym arOf resOf parOf \<Phi> intT intF intP"
proof-
  have UM: "UM_Model TE_wtFsym wtPsym TE_arOf TE_resOf parOf TE_\<Phi> D eintF eintP"
  unfolding UM_Model_def UM_Struct_def
  using M unfolding CU.Model_def CU.Struct_def U.Model_def
  using ProblemIkTpart.T_monotonic[OF P,
  unfolded TE_wtFsym_def[symmetric] TE_arOf_def[symmetric]
           TE_resOf_def[symmetric] TE_\<Phi>_def[symmetric]]
  by (auto simp: MonotProblem_def M_Problem_def M_Signature_def M.Problem_def)
  show ?thesis
  unfolding intT_def intF_def intP_def
  apply(rule ProblemIkTpart_TEModel.T_completeness)
  unfolding ProblemIkTpart_TEModel_def apply safe
  apply(rule P)
  apply(rule UM_Model.M_U_completeness)
  apply(rule UM[unfolded TE_wtFsym_def TE_arOf_def TE_resOf_def TE_\<Phi>_def])
  done
qed

text{* \ \\ \bf Completeness of the guard encodings \ \\ *}

theorem guards_completeness:
fixes wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list" and resOf :: "'fsym \<Rightarrow> 'tp" and parOf :: "'psym \<Rightarrow> 'tp list"
and \<Phi> :: "('fsym, 'psym) prob" and infTp :: "'tp \<Rightarrow> bool"
and tpD :: "'tp \<Rightarrow> bool" and tpFD :: "'tp \<Rightarrow> bool" and tpCD :: "'tp \<Rightarrow> bool"

and D :: "univ \<Rightarrow> bool"
and eintF :: "('fsym,'tp) G.efsym \<Rightarrow> univ list \<Rightarrow> univ"
and eintP :: "('psym,'tp) G.epsym \<Rightarrow> univ list \<Rightarrow> bool"

-- {* The problem translation (the same as in the case of soundness): *}
defines "GE_wtFsym \<equiv> ProblemIkTpartG.GE_wtFsym wtFsym resOf tpCD"
and "GE_wtPsym \<equiv> ProblemIkTpartG.GE_wtPsym wtPsym tpD tpFD"
and "GE_arOf \<equiv> ProblemIkTpartG.GE_arOf arOf"
and "GE_resOf \<equiv> ProblemIkTpartG.GE_resOf resOf"
and "GE_parOf \<equiv> ProblemIkTpartG.GE_parOf parOf"
defines "GE_\<Phi> \<equiv> ProblemIkTpartG.gPB wtFsym arOf resOf \<Phi> tpD tpFD tpCD"
and "U_arOf \<equiv> length \<circ> GE_arOf"
and "U_parOf \<equiv> length \<circ> GE_parOf"
defines "U_\<Phi> \<equiv> GE_\<Phi>"

-- {* The backward model translation: *}
defines "intT \<equiv> ProblemIkTpartG_GEModel.intT tpD tpFD (\<lambda>\<sigma>::'tp. D) eintP"
and "intF \<equiv> ProblemIkTpartG_GEModel.intF eintF"
and "intP \<equiv> ProblemIkTpartG_GEModel.intP eintP"

assumes
P: "ProblemIkTpartG wtFsym wtPsym arOf resOf parOf \<Phi> infTp tpD tpFD tpCD" and
M: "CU.Model GE_wtFsym GE_wtPsym (length o GE_arOf)
            (length o GE_parOf) GE_\<Phi> D eintF eintP"

shows "CM.Model wtFsym wtPsym arOf resOf parOf \<Phi> intT intF intP"
proof-
  have UM: "UM_Model GE_wtFsym GE_wtPsym GE_arOf GE_resOf GE_parOf GE_\<Phi> D eintF eintP"
  unfolding UM_Model_def UM_Struct_def
  using M unfolding CU.Model_def CU.Struct_def U.Model_def
  using ProblemIkTpartG.G_monotonic[OF P,
  unfolded GE_wtFsym_def[symmetric] GE_arOf_def[symmetric]
           GE_wtPsym_def[symmetric] GE_parOf_def[symmetric]
           GE_resOf_def[symmetric] GE_\<Phi>_def[symmetric]]
  by (auto simp: MonotProblem_def M_Problem_def M_Signature_def M.Problem_def)
  show ?thesis
  unfolding intT_def intF_def intP_def
  apply(rule ProblemIkTpartG_GEModel.G_completeness)
  unfolding ProblemIkTpartG_GEModel_def apply safe
  apply(rule P)
  apply(rule UM_Model.M_U_completeness)
  apply(rule UM[unfolded GE_wtFsym_def GE_wtPsym_def GE_parOf_def
             GE_arOf_def GE_resOf_def GE_\<Phi>_def])
  done
qed

end
