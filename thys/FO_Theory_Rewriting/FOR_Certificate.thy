theory FOR_Certificate
  imports Rewriting
begin

section \<open>Certificate syntax and type declarations\<close>

type_alias fvar = nat              \<comment> \<open>variable id\<close>
datatype ftrs = Fwd nat | Bwd nat  \<comment> \<open>TRS id and direction\<close>

definition map_ftrs where
  "map_ftrs f = case_ftrs (Fwd \<circ> f) (Bwd \<circ> f)"

subsection \<open>GTT relations\<close>

(* note: the 'trs will always be trs, but this way we get map functions for free *)

datatype 'trs gtt_rel                    \<comment> \<open>GTT relations\<close>
  = ARoot "'trs list"                    \<comment> \<open>root steps\<close>
  | GInv "'trs gtt_rel"                  \<comment> \<open>inverse of anchored or ordinary GTT relation\<close>
  | AUnion "'trs gtt_rel" "'trs gtt_rel" \<comment> \<open>union of anchored GTT relation\<close>
  | ATrancl "'trs gtt_rel"               \<comment> \<open>transitive closure of anchored GTT relation\<close>
  | GTrancl "'trs gtt_rel"               \<comment> \<open>transitive closure of ordinary GTT relation\<close>
  | AComp "'trs gtt_rel" "'trs gtt_rel"  \<comment> \<open>composition of anchored GTT relations\<close>
  | GComp "'trs gtt_rel" "'trs gtt_rel"  \<comment> \<open>composition of ordinary GTT relations\<close>

(* derived constructs *)
definition GSteps where "GSteps trss = GTrancl (ARoot trss)"


subsection \<open>RR1 and RR2 relations\<close>

datatype pos_step \<comment> \<open>position specification for lifting anchored GTT relation\<close>
  = PRoot         \<comment> \<open>allow only root steps\<close>
  | PNonRoot      \<comment> \<open>allow only non-root steps\<close>
  | PAny          \<comment> \<open>allow any position\<close>

datatype ext_step   \<comment> \<open>kind of rewrite steps for lifting anchored GTT relation\<close>
  = ESingle         \<comment> \<open>single steps\<close>
  | EParallel       \<comment> \<open>parallel steps, allowing the empty step\<close>
  | EStrictParallel \<comment> \<open>parallel steps, no allowing the empty step\<close>

datatype 'trs rr1_rel                     \<comment> \<open>RR1 relations, aka regular tree languages\<close>
  = R1Terms                               \<comment> \<open>all terms as RR1 relation (regular tree languages)\<close>
  | R1NF "'trs list"                      \<comment> \<open>direct normal form construction wrt. single steps\<close>
  | R1Inf "'trs rr2_rel"                  \<comment> \<open>infiniteness predicate\<close>
  | R1Proj nat "'trs rr2_rel"             \<comment> \<open>projection of RR2 relation\<close>
  | R1Union "'trs rr1_rel" "'trs rr1_rel" \<comment> \<open>union of RR1 relations\<close>
  | R1Inter "'trs rr1_rel" "'trs rr1_rel" \<comment> \<open>intersection of RR1 relations\<close>
  | R1Diff "'trs rr1_rel" "'trs rr1_rel"  \<comment> \<open>difference of RR1 relations\<close>
and 'trs rr2_rel                          \<comment> \<open>RR2 relations\<close>
  = R2GTT_Rel "'trs gtt_rel" pos_step ext_step \<comment> \<open>lifted GTT relations\<close>
  | R2Diag "'trs rr1_rel"                 \<comment> \<open>diagonal relation\<close>
  | R2Prod "'trs rr1_rel" "'trs rr1_rel"  \<comment> \<open>Cartesian product\<close>
  | R2Inv "'trs rr2_rel"                  \<comment> \<open>inverse of RR2 relation\<close>
  | R2Union "'trs rr2_rel" "'trs rr2_rel" \<comment> \<open>union of RR2 relations\<close>
  | R2Inter "'trs rr2_rel" "'trs rr2_rel" \<comment> \<open>intersection of RR2 relations\<close>
  | R2Diff "'trs rr2_rel" "'trs rr2_rel"  \<comment> \<open>difference of RR2 relations\<close>
  | R2Comp "'trs rr2_rel" "'trs rr2_rel"  \<comment> \<open>composition of RR2 relations\<close>

(* derived constructs *)
definition R1Fin where                    \<comment> \<open>finiteness predicate\<close>
  "R1Fin r = R1Diff R1Terms (R1Inf r)"
definition R2Eq where                     \<comment> \<open>equality\<close>
  "R2Eq = R2Diag R1Terms"
definition R2Reflc where                  \<comment> \<open>reflexive closure\<close>
  "R2Reflc r = R2Union r R2Eq"
definition R2Step where                   \<comment> \<open>single step $\to$\<close>
  "R2Step trss = R2GTT_Rel (ARoot trss) PAny ESingle"
definition R2StepEq where                 \<comment> \<open>at most one step $\to^=$\<close>
  "R2StepEq trss = R2Reflc (R2Step trss)"
definition R2Steps where                  \<comment> \<open>at least one step $\to^+$\<close>
  "R2Steps trss = R2GTT_Rel (GSteps trss) PAny EStrictParallel"
definition R2StepsEq where                \<comment> \<open>many steps $\to^*$\<close>
  "R2StepsEq trss = R2GTT_Rel (GSteps trss) PAny EParallel"
definition R2StepsNF where                \<comment> \<open>rewrite to normal form $\to^!$\<close>
  "R2StepsNF trss = R2Inter (R2StepsEq trss) (R2Prod R1Terms (R1NF trss))"
definition R2ParStep where                \<comment> \<open>parallel step\<close>
  "R2ParStep trss = R2GTT_Rel (ARoot trss) PAny EParallel"
definition R2RootStep where               \<comment> \<open>root step $\to_\epsilon$\<close>
  "R2RootStep trss = R2GTT_Rel (ARoot trss) PRoot ESingle"
definition R2RootStepEq where             \<comment> \<open>at most one root step $\to_\epsilon^=$\<close>
  "R2RootStepEq trss = R2Reflc (R2RootStep trss)"
  (* alternatively R2GTT_Rel (ARoot trss) PRoot SParallel *)
definition R2RootSteps where              \<comment> \<open>at least one root step $\to_\epsilon^+$\<close>
  "R2RootSteps trss = R2GTT_Rel (ATrancl (ARoot trss)) PRoot ESingle"
definition R2RootStepsEq where            \<comment> \<open>many root steps $\to_\epsilon^*$\<close>
  "R2RootStepsEq trss = R2Reflc (R2RootSteps trss)"
definition R2NonRootStep where            \<comment> \<open>non-root step $\to_{>\epsilon}$\<close>
  "R2NonRootStep trss = R2GTT_Rel (ARoot trss) PNonRoot ESingle"
definition R2NonRootStepEq where          \<comment> \<open>at most one non-root step $\to_{>\epsilon}^=$\<close>
  "R2NonRootStepEq trss = R2Reflc (R2NonRootStep trss)"
definition R2NonRootSteps where           \<comment> \<open>at least one non-root step $\to_{>\epsilon}^+$\<close>
  "R2NonRootSteps trss = R2GTT_Rel (GSteps trss) PNonRoot EStrictParallel"
definition R2NonRootStepsEq where         \<comment> \<open>many non-root steps $\to_{>\epsilon}^*$\<close>
  "R2NonRootStepsEq trss = R2GTT_Rel (GSteps trss) PNonRoot EParallel"
definition R2Meet where                   \<comment> \<open>meet $\uparrow$\<close>
  "R2Meet trss = R2GTT_Rel (GComp (GInv (GSteps trss)) (GSteps trss)) PAny EParallel"
definition R2Join where                   \<comment> \<open>join $\downarrow$\<close>
  "R2Join trss = R2GTT_Rel (GComp (GSteps trss) (GInv (GSteps trss))) PAny EParallel"


subsection \<open>Formulas\<close>

datatype 'trs formula             \<comment> \<open>formulas\<close>
  = FRR1 "'trs rr1_rel" fvar      \<comment> \<open>application of RR1 relation\<close>
  | FRR2 "'trs rr2_rel" fvar fvar \<comment> \<open>application of RR2 relation\<close>
  | FAnd "('trs formula) list"    \<comment> \<open>conjunction\<close>
  | FOr "('trs formula) list"     \<comment> \<open>disjunction\<close>
  | FNot "'trs formula"           \<comment> \<open>negation\<close>
  | FExists "'trs formula"        \<comment> \<open>existential quantification\<close>
  | FForall "'trs formula"        \<comment> \<open>universal quantification\<close>

(* derived constructs *)
definition FTrue where            \<comment> \<open>true\<close>
  "FTrue \<equiv> FAnd []"
definition FFalse where           \<comment> \<open>false\<close>
  "FFalse \<equiv> FOr []"
(* FRestrict can be defined, but we may want to do out of bounds checking later *)
definition FRestrict where      \<comment> \<open>reorder/rename/restrict TRSs for subformula\<close>
  "FRestrict f trss \<equiv> map_formula (map_ftrs (\<lambda>n. if n \<ge> length trss then 0 else trss ! n)) f"


subsection \<open>Signatures and Problems\<close>

datatype ('f, 'v, 't) many_sorted_sig
  = Many_Sorted_Sig (ms_functions: "('f \<times> 't list \<times> 't) list") (ms_variables: "('v \<times> 't) list")

datatype ('f, 'v, 't) problem
  = Problem (p_signature: "('f, 'v, 't) many_sorted_sig")
            (p_trss: "('f, 'v) trs list")
            (p_formula: "ftrs formula")


subsection \<open>Proofs\<close>

datatype equivalence \<comment> \<open>formula equivalences\<close>
  = EDistribAndOr    \<comment> \<open>distributivity: conjunction over disjunction\<close>
  | EDistribOrAnd    \<comment> \<open>distributivity: disjunction over conjunction\<close>

datatype 'trs inference           \<comment> \<open>inference rules for formula creation\<close>
  = IRR1 "'trs rr1_rel" fvar      \<comment> \<open>formula from RR1 relation\<close>
  | IRR2 "'trs rr2_rel" fvar fvar \<comment> \<open>formula from RR2 relation\<close>
  | IAnd "nat list"               \<comment> \<open>conjunction\<close>
  | IOr "nat list"                \<comment> \<open>disjunction\<close>
  | INot nat                      \<comment> \<open>negation\<close>
  | IExists nat                   \<comment> \<open>existential quantification\<close>
  | IRename nat "fvar list"       \<comment> \<open>permute variables\<close>
  | INNFPlus nat                  \<comment> \<open>equivalence modulo negation normal form plus ACIU0 for $\land$ and $\lor$\<close>
  | IRepl equivalence "nat list" nat \<comment> \<open>replacement according to given equivalence\<close>

datatype claim = Empty | Nonempty

datatype info = Size nat nat nat

datatype 'trs certificate
  = Certificate "(nat \<times> 'trs inference \<times> 'trs formula \<times> info list) list" claim nat


subsection \<open>Example\<close>

definition no_normal_forms_cert :: "ftrs certificate" where
  "no_normal_forms_cert = Certificate
  [ (0, (IRR2 (R2Step [Fwd 0]) 1 0),
        (FRR2 (R2Step [Fwd 0]) 1 0), [])
  , (1, (IExists 0),
        (FExists (FRR2 (R2Step [Fwd 0]) 1 0)), [])
  , (2, (INot 1),
        (FNot (FExists (FRR2 (R2Step [Fwd 0]) 1 0))), [])
  , (3, (IExists 2),
        (FExists (FNot (FExists (FRR2 (R2Step [Fwd 0]) 1 0)))), [])
  , (4, (INot 3),
        (FNot (FExists (FNot (FExists (FRR2 (R2Step [Fwd 0]) 1 0))))), [])
  , (5, (INNFPlus 4),
        (FForall (FExists (FRR2 (R2Step [Fwd 0]) 1 0))), [])
  ] Nonempty 5"

definition no_normal_forms_problem :: "(string, string, unit) problem" where
  "no_normal_forms_problem = Problem
    (Many_Sorted_Sig [(''f'',[()],()), (''a'',[],())] [(''x'',())])
    [{(Fun ''f'' [Var ''x''],Fun ''a'' [])}]
    (FForall (FExists (FRR2 (R2Step [Fwd 0]) 1 0)))"

end