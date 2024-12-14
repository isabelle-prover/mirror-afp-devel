section "Completeness"

theory Completeness
imports Tree Sequents
begin


subsection "pseq: type represents a processed sequent"

type_synonym "atom"  = "(signs * predicate * vbl list)"
type_synonym nform = "(nat * formula)"
type_synonym pseq  = "(atom list * nform list)"

definition
  sequent :: "pseq \<Rightarrow> formula list" where
  "sequent = (\<lambda>(atoms,nforms) . map snd nforms @ map (\<lambda>(z,p,vs) . FAtom z p vs) atoms)"

definition
  pseq :: "formula list \<Rightarrow> pseq" where
  "pseq fs = ([],map (\<lambda>f.(0,f)) fs)"

definition atoms :: "pseq \<Rightarrow> atom list" where "atoms = fst"
definition nforms :: "pseq \<Rightarrow> nform list" where "nforms = snd"


subsection "subs: SATAxiom"

definition
  SATAxiom :: "formula list \<Rightarrow> bool" where
  "SATAxiom fs \<equiv> (\<exists>n vs . FAtom Pos n vs \<in> set fs \<and> FAtom Neg n vs \<in> set fs)"


subsection "subs: a CutFreePC justifiable backwards proof step"

definition
  subsFAtom :: "[atom list,(nat * formula) list,signs,predicate,vbl list] \<Rightarrow> pseq set" where
  "subsFAtom atms nAs z P vs = { ((z,P,vs)#atms,nAs) }"

definition
  subsFConj :: "[atom list,(nat * formula) list,signs,formula,formula] \<Rightarrow> pseq set" where
  "subsFConj atms nAs z A0 A1 =
    (case z of
      Pos \<Rightarrow> { (atms,(0,A0)#nAs),(atms,(0,A1)#nAs) }
    | Neg \<Rightarrow> { (atms,(0,A0)#(0,A1)#nAs) })"

definition
  subsFAll :: "[atom list,(nat * formula) list,nat,signs,formula,vbl set] \<Rightarrow> pseq set" where
  "subsFAll atms nAs n z A frees =
    (case z of
      Pos \<Rightarrow> { let v = freshVar frees in  (atms,(0,instanceF v A)#nAs) }
    | Neg \<Rightarrow> { (atms,(0,instanceF (X n) A)#nAs @ [(Suc n,FAll Neg A)]) })"
    
definition
  subs :: "pseq \<Rightarrow> pseq set" where
  "subs = (\<lambda>pseq .
             if SATAxiom (sequent pseq) then
                 {}
             else let (atms,nforms) = pseq
                  in  case nforms of
                         []     \<Rightarrow> {}
                       | nA#nAs \<Rightarrow> let (n,A) = nA
                                   in  (case A of
                                            FAtom z P vs  \<Rightarrow> subsFAtom atms nAs z P vs
                                          | FConj z A0 A1 \<Rightarrow> subsFConj atms nAs z A0 A1
                                          | FAll  z A     \<Rightarrow> subsFAll  atms nAs n z A (freeVarsFL (sequent pseq))))"


subsection "proofTree(Gamma) says whether tree(Gamma) is a proof"

definition
  proofTree :: "(nat * pseq) set \<Rightarrow> bool" where
  "proofTree A \<longleftrightarrow> bounded A \<and> founded subs (SATAxiom \<circ> sequent) A"


subsection "path: considers, contains, costBarrier"

definition
  considers :: "[nat \<Rightarrow> pseq,nat * formula,nat] \<Rightarrow> bool" where
  "considers f nA n = (case (snd (f n)) of [] \<Rightarrow> False | x#xs \<Rightarrow> x=nA)"

definition
  "contains" :: "[nat \<Rightarrow> pseq,nat * formula,nat] \<Rightarrow> bool" where
  "contains f nA n \<longleftrightarrow> nA \<in> set (snd (f n))"

abbreviation (input) "power3 \<equiv> power (3::nat)"

definition
  costBarrier :: "[nat * formula,pseq] \<Rightarrow> nat" where
    (******
     costBarrier justifies: eventually contains \<Longrightarrow> eventually considers
     with a termination thm, (barrier strictly decreases in |N).
     ******)
  "costBarrier nA = (\<lambda>(atms,nAs).
    let barrier = takeWhile (\<lambda>x. nA \<noteq> x) nAs
    in  let costs = map (power3 \<circ> size \<circ> snd) barrier
    in  sumList costs)"


subsection "path: eventually"

(******
 Could do this with composable temporal operators, but following paper proof first.
 ******)

definition
  EV :: "[nat \<Rightarrow> bool] \<Rightarrow> bool" where
  "EV f \<equiv> (\<exists>n . f n)"


subsection "path: counter model"

definition
  counterM :: "(nat \<Rightarrow> pseq) \<Rightarrow> object set" where
  "counterM f \<equiv> range obj"

definition
  counterEvalP :: "(nat \<Rightarrow> pseq) \<Rightarrow> predicate \<Rightarrow> object list \<Rightarrow> bool" where
  "counterEvalP f = (\<lambda>p args . ! i . \<not> (EV (contains f (i,FAtom Pos p (map (X \<circ> inv obj) args)))))"

definition
  counterModel :: "(nat \<Rightarrow> pseq) \<Rightarrow> model" where
  "counterModel f = Abs_model (counterM f, counterEvalP f)"


primrec counterAssign :: "vbl \<Rightarrow> object"
  where "counterAssign (X n) = obj n"  (* just deX *)


subsection "subs: finite"
  
lemma finite_subs: "finite (subs \<gamma>)"
  by (simp add: subs_def subsFAtom_def subsFConj_def subsFAll_def split_beta split: list.split formula.split signs.split)

lemma fansSubs: "fans subs"
  by (simp add: fans_def finite_subs)

lemma subs_def2:  
"\<not> SATAxiom (sequent \<gamma>) \<Longrightarrow>
   subs \<gamma> = 
    (case nforms \<gamma> of 
         []     \<Rightarrow> {} 
       | nA#nAs \<Rightarrow> let (n,A) = nA 
                   in  (case A of 
                          FAtom z P vs  \<Rightarrow> subsFAtom (atoms \<gamma>) nAs z P vs 
                        | FConj z A0 A1 \<Rightarrow> subsFConj (atoms \<gamma>) nAs z A0 A1 
                        | FAll  z A     \<Rightarrow> subsFAll  (atoms \<gamma>) nAs n z A (freeVarsFL (sequent \<gamma>))))"
  by (simp add: subs_def nforms_def atoms_def split_beta split: list.split)


subsection "inherited: proofTree"

lemma proofTree_def2: "proofTree = (\<lambda>x. bounded x \<and> founded subs (SATAxiom \<circ> sequent) x)"
  by (force simp add: proofTree_def) 

lemma inheritedProofTree: "inherited subs proofTree"
  using inheritedBounded inheritedFounded inheritedJoinI proofTree_def by blast

lemma proofTreeI: "\<lbrakk>bounded A; founded subs (SATAxiom \<circ> sequent) A\<rbrakk> \<Longrightarrow> proofTree A"
  by (simp add: proofTree_def)

lemma proofTreeBounded: "proofTree A \<Longrightarrow> bounded A"
  using proofTree_def by blast

lemma proofTreeTerminal: 
  "\<lbrakk>proofTree A; (n, delta) \<in> A; terminal subs delta\<rbrakk> \<Longrightarrow> SATAxiom (sequent delta)"
  by(force simp add: proofTree_def founded_def)


subsection "pseq: lemma"

lemma snd_o_Pair: "(snd \<circ> (Pair x)) = (\<lambda>x. x)"
  by auto

lemma sequent_pseq: "sequent (pseq fs) = fs"
  by (simp add: pseq_def sequent_def snd_o_Pair)

subsection "SATAxiom: proofTree"
    
lemma SATAxiomTerminal[rule_format]: "SATAxiom (sequent \<gamma>) \<Longrightarrow> terminal subs \<gamma>"
  by (simp add: subs_def proofTree_def terminal_def founded_def bounded_def)

lemma SATAxiomBounded:"SATAxiom (sequent \<gamma>) \<Longrightarrow> bounded (tree subs \<gamma>)"
  by (metis (lifting) boundedInsert equals0D finite.simps inheritedBounded
      inheritedUNEq subs_def treeEquation)

lemma SATAxiomFounded: "SATAxiom (sequent \<gamma>) \<Longrightarrow> founded subs (SATAxiom \<circ> sequent) (tree subs \<gamma>)"
  apply (clarsimp simp add: founded_def split: prod.splits)
  by (metis SATAxiomTerminal terminalI tree.cases tree1Eq)

lemma SATAxiomProofTree: "SATAxiom (sequent \<gamma>) \<Longrightarrow> proofTree (tree subs \<gamma>)"
  by (blast intro: proofTreeI SATAxiomBounded SATAxiomFounded)

lemma SATAxiomEq: "(proofTree (tree subs \<gamma>) \<and> terminal subs \<gamma>) = SATAxiom (sequent \<gamma>)"
  using SATAxiomProofTree SATAxiomTerminal proofTreeTerminal tree.tree0 by blast


subsection "SATAxioms are deductions: - needed"

lemma SAT_deduction: 
  assumes "SATAxiom x"
  shows "x \<in> deductions CutFreePC"
proof -
  obtain n vs where "FAtom Pos n vs \<in> set x" and "FAtom Neg n vs \<in> set x"
    using SATAxiom_def assms by blast
  with inDed_mono [where x="[FAtom Pos n vs,FAtom Neg n vs]"]
  show ?thesis
    by (simp add: AxiomI rulesInPCs(2))
qed
  

subsection "proofTrees are deductions: subs respects rules - messy start and end"

lemma subsJustified': 
  notes ss = subs_def2 nforms_def Let_def atoms_def sequent_def subsFAtom_def subsFConj_def subsFAll_def
  shows "\<lbrakk>\<not> SATAxiom (sequent (ats, (n, f) # list));
          \<not> terminal subs (ats, (n, f) # list);
          \<forall>sigma\<in>subs (ats, (n, f) # list). sequent sigma \<in> deductions CutFreePC\<rbrakk>
         \<Longrightarrow> sequent (ats, (n, f) # list) \<in> deductions CutFreePC"
proof (induction f rule: formula_signs_induct)
  case (FAllP A)
  then show ?case
        by (simp add: ss PermI rulesInPCs freshVarI AllI)
next
  case (FAllN A)
  have *: "Exs \<subseteq> CutFreePC" "Contrs \<subseteq> CutFreePC"
    using rulesInPCs by blast+
  moreover 
  have "instanceF (X n) A # map snd list @ FAll Neg A # map (\<lambda>(z, x, y). FAtom z x y) ats
            \<in> deductions CutFreePC"
    using FAllN by (simp add: ss)
  then have "instanceF (X n) A # FAll Neg A # map snd list @ map (\<lambda>(z, x, y). FAtom z x y) ats
    \<in> deductions CutFreePC"
    by (simp add: PermI rulesInPCs(16))
  ultimately show ?case
    by (simp add: ContrI ExI sequent_def)
qed (simp_all add: ss PermI rulesInPCs ConjI' DisjI)

lemma subsJustified:
  assumes "\<not> terminal subs \<gamma>"
    and "\<forall>sigma \<in> subs \<gamma>. sequent sigma \<in> deductions (CutFreePC)"
  shows "sequent \<gamma> \<in> deductions (CutFreePC)"
proof(cases "SATAxiom (sequent \<gamma>)")
  case True
  then show ?thesis using SAT_deduction by blast
next
  case False
  show ?thesis 
  proof (cases \<gamma>)
    case (Pair ats nfs)
    show ?thesis
    proof (cases nfs)
      case Nil
      then show ?thesis
        using False Pair assms nforms_def subs_def2 terminal_def by force 
    next
      case (Cons a list)
      then show ?thesis
        by (metis False Pair assms subsJustified' surj_pair) 
    qed
  qed
qed

subsection "proofTrees are deductions: instance of boundedTreeInduction"

lemmas proofTreeD = proofTree_def [THEN iffD1]

lemma proofTreeDeductionD:
  assumes "proofTree(tree subs \<gamma>)"
  shows "sequent \<gamma> \<in> deductions (CutFreePC)"
proof (rule boundedTreeInduction [OF fansSubs])
  show "bounded (tree subs \<gamma>)"
    by (simp add: assms proofTreeBounded)
next
  show "founded subs (\<lambda>a. sequent a \<in> deductions CutFreePC) (tree subs \<gamma>)"
    by (metis (no_types, lifting) SAT_deduction assms comp_def foundedMono
        proofTreeD)
qed (use subsJustified in auto)


subsection "contains, considers:"

lemma contains_def2: "contains f iA n = (iA \<in> set (nforms (f n)))"
  using Completeness.contains_def nforms_def by presburger

lemma considers_def2: "considers f iA n = ( \<exists>nAs . nforms (f n) = iA#nAs)"
  by (simp add: considers_def nforms_def split: list.split) 

lemmas containsI = contains_def2[THEN iffD2]


subsection "path: nforms = [] implies"

lemma nformsNoContains: 
  "nforms (f n) = [] \<Longrightarrow> \<not> contains f iA n"
  by (simp add: contains_def2) 

lemma nformsTerminal: "nforms (f n) = [] \<Longrightarrow> terminal subs (f n)"
  by (simp add: subs_def Let_def terminal_def nforms_def split_beta)

lemma nformsStops: 
  "\<lbrakk>branch subs \<gamma> f; \<And>n. \<not> proofTree (tree subs (f n)); nforms (f n) = []\<rbrakk>
  \<Longrightarrow> nforms (f (Suc n)) = [] \<and> atoms (f (Suc n)) = atoms (f n)"
  by (metis (lifting) SATAxiomProofTree branch_def empty_iff list.case(1)
      subs_def2)


subsection "path: cases"

lemma terminalNFormCases: "terminal subs (f n) \<or> (\<exists>i A nAs . nforms (f n) = (i,A)#nAs)"
  by (metis (lifting) list.case(1) neq_Nil_conv subs_def subs_def2 surj_pair
      terminal_def)

lemma cases[elim_format]: "terminal subs (f n) \<or> (\<not> (terminal subs (f n) \<and> (\<exists>i A nAs . nforms (f n) = (i,A)#nAs)))"
  by simp


subsection "path: contains not terminal and propagate condition"
    
lemma containsNotTerminal:
  assumes "branch subs \<gamma> f" "\<not> proofTree (tree subs (f n))" "contains f iA n"
  shows "\<not> terminal subs (f n)"
proof (cases "SATAxiom (sequent (f n))")
  case True
  then show ?thesis
    using SATAxiomEq assms by blast
next
  case False
  then show ?thesis
    using assms
    by (auto simp: subs_def subsFAtom_def subsFConj_def subsFAll_def contains_def terminal_def split_beta 
        split: list.split signs.split formula.splits)
qed

lemma containsPropagates:
  assumes "branch subs \<gamma> f"
      and "\<And>n. \<not> proofTree (tree subs (f n))"
      and "contains f iA n"
  shows "contains f iA (Suc n) \<or> considers f iA n"
proof -
  have \<section>: "f (Suc n) \<in> subs (f n)"
    by (meson assms branchSubs containsNotTerminal)
  then show ?thesis
  proof (cases "considers f iA n")
    case True
    then show ?thesis
      by blast
  next
    case ncons: False
    show ?thesis
    proof (cases "SATAxiom (sequent (f n))")
      case True
      then show ?thesis
        using SATAxiomEq assms by blast 
    next
      case False
      with assms \<section> show ?thesis
        by (auto simp: subs_def2 contains_def considers_def2 nforms_def 
                       subsFAtom_def subsFConj_def subsFAll_def  
            split: list.splits formula.splits signs.splits)
    qed
  qed
qed



subsection "termination: (for EV contains implies EV considers)"

lemma terminationRule [rule_format]:
  "! n. P n \<longrightarrow> (\<not> (P (Suc n)) | (P (Suc n) \<and> msrFn (Suc n) < (msrFn::nat \<Rightarrow> nat) n)) \<Longrightarrow> P m \<longrightarrow> (\<exists>n . P n \<and> \<not> (P (Suc n)))"
  (is "_ \<Longrightarrow> ?P m") 
using measure_induct_rule[of msrFn "?P" m]
  by blast


subsection "costBarrier: lemmas"

subsection "costBarrier: exp3 lemmas - bit specific..."

lemma exp1: "power3 A + power3 B < 3 * (power3 A * power3 B)" 
  by (induction A) (use less_2_cases not_less_eq in fastforce)+


lemma exp1': "power3 A < 3 * ((power3 A) * (power3 B)) + C"
  by (meson add_lessD1 exp1 trans_less_add1)

lemma exp2: "Suc 0 < 3 * power3 (B)"
  by (simp add: Suc_lessI) 


subsection "costBarrier: decreases whilst contains and unconsiders"

lemma costBarrierDecreases':
  notes ss = subs_def2 nforms_def subsFAtom_def subsFConj_def subsFAll_def costBarrier_def 
  shows "\<lbrakk>\<not> SATAxiom (sequent (a, (num, fm) # list)); iA \<noteq> (num, fm);
          \<not> proofTree (tree subs (a, (num, fm) # list));
          fSucn \<in> subs (a, (num, fm) # list); iA \<in> set list\<rbrakk>
         \<Longrightarrow> costBarrier iA fSucn < costBarrier iA (a, (num, fm) # list)"
proof (induction fm rule: formula_signs_induct)
  case (FConjP A B)
  then show ?case
    by (auto simp: ss exp2 power_add)
next
  case (FConjN A B)
  with exp1' show ?case 
    by (simp add: ss exp1 power_add)
qed (auto simp: ss size_instance)

lemma costBarrierDecreases: 
  assumes "branch subs \<gamma> f"
    and "\<And>n. \<not> proofTree (tree subs (f n))"
    and "contains f iA n"
    and "\<not> considers f iA n"
  shows "costBarrier iA (f (Suc n)) < costBarrier iA (f n)" 
proof -
  have 1: "\<not> terminal subs (f n)"
    using assms containsNotTerminal by blast
  have "\<not> SATAxiom (sequent (f n))"
    using SATAxiomTerminal 1 by blast
  moreover have "f (Suc n) \<in> subs (f n)"
    by (meson assms(1) branchSubs 1)
  ultimately show ?thesis
    using assms
    unfolding contains_def considers_def2 nforms_def
    by (metis costBarrierDecreases' eq_snd_iff list.set_cases )
qed


subsection "path: EV contains implies EV considers"

lemma considersContains: "considers f iA n \<Longrightarrow> contains f iA n"
  using considers_def2 contains_def2 by auto

lemma containsConsiders:
  assumes "branch subs \<gamma> f"
    and "\<And>n. \<not> proofTree (tree subs (f n))"
    and "EV (contains f iA)"
  shows "EV (considers f iA)"
proof (rule ccontr)
  assume non: "\<not> EV (considers f iA)"
  then obtain n where "contains f iA n \<and> \<not> considers f iA n"
    using EV_def assms by fastforce
  then have "\<exists>n'. (contains f iA n' \<and> \<not> considers f iA n') \<and>
           \<not> (contains f iA (Suc n') \<and> \<not> considers f iA (Suc n'))"
    using assms costBarrierDecreases
    by (intro terminationRule [where msrFn= "\<lambda>n. costBarrier iA (f n)"]; blast)
  with assms show False
    by (metis EV_def non containsPropagates)
qed


subsection "EV contains: common lemma"

lemma lemmA: 
  assumes "branch subs \<gamma> f"
    and "\<And>n. \<not> proofTree (tree subs (f n))"
    and "EV (contains f (i, A))"
  obtains n nAs where "\<not> SATAxiom (sequent (f n))" 
                      "nforms (f n) = (i,A) # nAs" "f (Suc n) \<in> subs (f n)"
proof -
  obtain n where n: "considers f (i, A) n" "contains f (i, A) n"
    by (metis EV_def assms considersContains containsConsiders)
  with assms that show ?thesis
      by (metis SATAxiomTerminal considers_def2 branchSubs containsNotTerminal)
qed


subsection "EV contains: FConj,FDisj,FAll"

lemma evContainsConj:
  assumes "EV (contains f (i, FConj Pos A0 A1))"
    and "branch subs \<gamma> f"
    and "\<And>n. \<not> proofTree (tree subs (f n))"
  shows "EV (contains f (0, A0)) \<or> EV (contains f (0, A1))"
proof -
  obtain n nAs where "\<not> SATAxiom (sequent (f n))" 
                     "nforms (f n) = (i, FConj Pos A0 A1) # nAs" "f (Suc n) \<in> subs (f n)"
    by (metis assms lemmA)
  with assms have "EV (\<lambda>n. contains f (0,A0) n \<or> contains f (0,A1) n)"
    apply (simp add: EV_def contains_def subsFConj_def subs_def2)
    by (metis list.set_intros(1) snd_conv)
  then show ?thesis
    using EV_def by fastforce
qed

lemma evContainsDisj:
  assumes "EV (contains f (i, FConj Neg A0 A1))"
    and "branch subs \<gamma> f"
    and "\<And>n. \<not> proofTree (tree subs (f n))"
  shows "EV (contains f (0, A0)) \<and> EV (contains f (0, A1))"
proof -
  obtain n nAs where "\<not> SATAxiom (sequent (f n))" 
                     "nforms (f n) = (i, FConj Neg A0 A1) # nAs" "f (Suc n) \<in> subs (f n)"
    by (metis assms lemmA)
  with assms have "EV (\<lambda>n. contains f (0,A0) n \<and> contains f (0,A1) n)"
    apply (simp add: EV_def contains_def subsFConj_def subs_def2)
    by (metis list.set_intros snd_conv)
  then show ?thesis
    using EV_def by fastforce
qed

lemma evContainsAll:
  assumes "EV (contains f (i,FAll Pos body))"
    and "branch subs \<gamma> f"
    and "\<And>n. \<not> proofTree (tree subs (f n))"
  shows "\<exists>v . EV (contains f (0,instanceF v body))"
proof -
  obtain n nAs where "\<not> SATAxiom (sequent (f n))" 
                     "nforms (f n) = (i, FAll Pos body) # nAs" "f (Suc n) \<in> subs (f n)"
    by (metis assms lemmA)
  then have "(0, instanceF (freshVar (freeVarsFL (sequent (f n)))) body)
              \<in> set (snd (f (Suc n)))"
    by (simp add: contains_def subsFAll_def subs_def2)
  then show ?thesis
    unfolding EV_def
    by (metis containsI nforms_def)
qed

lemma evContainsEx_instance:
  assumes "EV (contains f (i,FAll Neg body))"
    and "branch subs \<gamma> f"
    and "\<And>n. \<not> proofTree (tree subs (f n))"
  shows "EV (contains f (0,instanceF (X i) body))"
proof -
  obtain n nAs where "\<not> SATAxiom (sequent (f n))" 
                     "nforms (f n) = (i, FAll Neg body) # nAs" "f (Suc n) \<in> subs (f n)"
    by (metis assms lemmA)
  then have "contains f (0, instanceF (X i) body) (Suc n)"
    by (simp add: containsI nforms_def subsFAll_def subs_def2)
  then show ?thesis
    unfolding EV_def
    by metis
qed

lemma evContainsEx_repeat:
  assumes "EV (contains f (i,FAll Neg body))"
    and "branch subs \<gamma> f"
    and "\<And>n. \<not> proofTree (tree subs (f n))"
  shows "EV (contains f (Suc i,FAll Neg body))"
proof -
  obtain n nAs where n: "\<not> SATAxiom (sequent (f n))" 
                     "nforms (f n) = (i, FAll Neg body) # nAs" "f (Suc n) \<in> subs (f n)"
    by (metis assms lemmA)
  then have "\<lbrakk>f (Suc n) = (atoms (f n), (0, instanceF (X i) body) # nAs @ [(Suc i, FAll Neg body)])\<rbrakk>
            \<Longrightarrow> \<exists>n. (Suc i, FAll Neg body) \<in> set (snd (f n))"
    by (metis in_set_conv_decomp list.set_intros(2) snd_conv)
  with assms n show ?thesis
    by (simp add: EV_def contains_def2 nforms_def subsFAll_def subs_def2)
qed


subsection "EV contains: lemmas (temporal related)"

(******
 Should have abstracted to have temporal ops:
    EV   \<in> (nat -> bool) -> nat -> bool
    AW   \<in> (nat -> bool) -> nat -> bool
    NEXT \<in> (nat -> bool) -> nat -> bool
 then require:
    EV P and EV B imp (\n. A n \<and> B n)
 ******)


subsection "EV contains: FAtoms"

lemma notTerminalNotSATAxiom: "\<not> terminal subs \<gamma> \<Longrightarrow> \<not> SATAxiom (sequent \<gamma>)"
  using SATAxiomTerminal by blast

lemma notTerminalNforms: "\<not> terminal subs (f n) \<Longrightarrow> nforms (f n) \<noteq> []"
  by (metis (lifting) list.simps(4) subs_def subs_def2 terminal_def)
    
lemma atomsPropagate:
  assumes f: "branch subs \<gamma> f" and x: "x \<in> set (atoms (f n))"
  shows "x \<in> set (atoms (f (Suc n)))"
proof (cases "terminal subs (f n)")
  case True
  then show ?thesis
    by (metis assms branchStops)
next
  case nonterm: False
  then have \<section>: "f (Suc n) \<in> subs (f n)"
    by (meson branchSubs f)
  show ?thesis
  proof (cases "nforms (f n)")
    case Nil
    then show ?thesis
      by (metis (lifting) "\<section>" empty_iff list.case(1) subs_def subs_def2)
  next
    case (Cons nfm list)
    with x nonterm \<section> show ?thesis
      by (force simp: subs_def2 atoms_def notTerminalNotSATAxiom 
          subsFAtom_def subsFConj_def subsFAll_def 
          split: signs.splits formula.splits)
  qed
qed

subsection "EV contains: FEx cases"

lemma evContainsEx0_allRepeats: 
  "\<lbrakk>branch subs \<gamma> f; \<And>n . \<not> proofTree (tree subs (f n));
     EV (contains f (0,FAll Neg A))\<rbrakk>
  \<Longrightarrow> EV (contains f (i,FAll Neg A))"
  by (induction i) (simp_all add: evContainsEx_repeat)

lemma evContainsEx0_allInstances:
  "\<lbrakk>branch subs \<gamma> f; \<And>n. \<not> proofTree (tree subs (f n));
     EV (contains f (0,FAll Neg A))\<rbrakk>
  \<Longrightarrow> EV (contains f (0,instanceF (X i) A))"
  using evContainsEx0_allRepeats evContainsEx_instance by blast

subsection "pseq: creates initial pseq"
    
lemma containsPSeq0D: "branch subs (pseq fs) f \<Longrightarrow> contains f (i,A) 0 \<Longrightarrow> i=0"
  by (simp add: branch_def contains_def2 image_iff nforms_def pseq_def)


subsection "EV contains: contain any (i,FEx y) means contain all (i,FEx y)"
    
(******
 Now, show (Suc i,FEx v A) present means (i,FEx v A) present (or at start).
 Assumes initial pseq contains only (0,form) pairs.
 ------
 Show that only way of introducing a (Suc i,FEx_) was from (i,FEx_).
 contains n == considers n or contains n+.

 Want to find the point where it was introduced.
 Have, P true all n or fails at 0 or for a (first) successor.

     (!n. P n) | (\<not> P 0) | (P n \<and> \<not> P (Suc n))

 Instance this with P n = \<not> (contains ..FEx.. n).
 ******)

lemma natPredCases: 
  obtains "\<forall>n. P n" | "\<not> P 0" | n where "P n" "\<not> P (Suc n)"
  using nat_induct by auto

lemma containsNotTerminal': 
  "\<lbrakk> branch subs \<gamma> f; \<And>n. \<not> proofTree (tree subs (f n)); contains f iA n \<rbrakk> \<Longrightarrow> \<not> (terminal subs (f n))"
  by (simp add: containsNotTerminal)

lemma evContainsExSuc_containsEx:
  assumes "branch subs (pseq fs) f"
    and "\<And>n. \<not> proofTree (tree subs (f n))"
    and "EV (contains f (Suc i, FAll Neg body))"
  shows "EV (contains f (i, FAll Neg body))"
  using natPredCases [of "\<lambda>n. \<not> contains f (Suc i,FAll Neg body) n"]
proof cases
  case 1
  with assms show ?thesis
    by (force simp: EV_def)
next
  case 2
  then show ?thesis
    using assms(1) containsPSeq0D by blast
next
  case (3 n)
  with assms have nonterm: "\<not> terminal subs (f n)"
    by (metis branchStops containsNotTerminal')
  then have f: "f (Suc n) \<in> subs (f n)"
    by (meson assms(1) branchSubs)
  have "considers f (i, FAll Neg body) n"
  proof (cases "SATAxiom (sequent (f n))")
    case True
    then show ?thesis
      using SATAxiomTerminal nonterm by blast
  next
    case False
    then obtain j A nAs where i: "snd (f n) = (j, A) # nAs"
      by (metis (lifting) nforms_def empty_iff f list.exhaust list.simps(4) subs_def2
          surj_pair)
    then have nf: "nforms (f n) \<noteq> []"
      by (simp add: nforms_def)
    have "snd (f n) = (k, A) # nAs \<longrightarrow> k = i \<and> A = FAll Neg body" for k A
      apply(induction A rule: formula_signs_induct)
      using i 3 f False 
      by(auto simp: subs_def2 nforms_def subsFAtom_def subsFConj_def subsFAll_def contains_def2)
    with nf show ?thesis
      by (auto simp add: considers_def i split: list.splits formula.splits signs.splits)
  qed
  then show ?thesis
    by (meson EV_def considersContains)
qed

subsection "EV contains: contain any (i,FEx y) means contain all (i,FEx y)"

lemma evContainsEx_containsEx0: 
  "\<lbrakk>branch subs (pseq fs) f; \<And>n. \<not> proofTree (tree subs (f n)); 
    EV (contains f (i,FAll Neg A))\<rbrakk>
   \<Longrightarrow> EV (contains f (0,FAll Neg A))"
proof (induction i)
  case 0
  then show ?case by simp
next
  case (Suc i)
  then show ?case
    using evContainsExSuc_containsEx by blast
qed

lemma evContainsExval: 
  "\<lbrakk>EV (contains f (i,FAll Neg body)); branch subs (pseq fs) f; 
    \<And>n. \<not> proofTree (tree subs (f n))\<rbrakk> 
  \<Longrightarrow> EV (contains f (0,instanceF v body))"
    by (induction v) (simp add: evContainsEx0_allInstances evContainsEx_containsEx0)


subsection "EV contains: atoms"

lemma atomsInSequentI: 
  "(z,P,vs) \<in> set (fst ps) \<Longrightarrow> FAtom z P vs \<in> set (sequent ps)"
  by (fastforce simp add: sequent_def fst_def split: prod.split)
    
lemma evContainsAtom1: 
  assumes "branch subs (pseq fs) f"
    and "\<And>n. \<not> proofTree (tree subs (f n))"
    and "EV (contains f (i, FAtom z P vs))"
    shows "\<exists>n. (z, P, vs) \<in> set (fst (f n))"
proof -
  obtain n nAs where "\<not> SATAxiom (sequent (f n))" 
                     "nforms (f n) = (i, FAtom z P vs) # nAs" 
                     "f (Suc n) \<in> subs (f n)"
    by (metis assms lemmA)
  then have "(z, P, vs) \<in> set (fst (f (Suc n)))"
    by (simp add: subsFAtom_def subs_def2)
  then show ?thesis ..
qed
    
lemmas atomsPropagate' = atomsPropagate[simplified atoms_def, simplified]

lemma evContainsAtom: 
  assumes "branch subs (pseq fs) f"
    and "\<And>n. \<not> proofTree (tree subs (f n))"
    and "EV (contains f (i, FAtom z P vs))"
    shows "\<exists>n. \<forall>m. FAtom z P vs \<in> set (sequent (f (n + m)))"
proof -
  obtain n where n: "(z, P, vs) \<in> set (fst (f n))"
    using assms evContainsAtom1 by blast
  then have "(z, P, vs) \<in> set (fst (f (n + m)))" for m
  by  (induction m) (use assms atomsPropagate' in auto)
  then show ?thesis
    using atomsInSequentI by blast
qed

lemma notEvContainsBothAtoms: 
  "\<lbrakk>branch subs (pseq fs) f; \<And>n . \<not> proofTree (tree subs (f n))\<rbrakk>
  \<Longrightarrow> \<not> EV (contains f (i,FAtom Pos p vs)) \<or>
      \<not> EV (contains f (j,FAtom Neg p vs))"
  by (metis SATAxiomProofTree SATAxiom_def add.commute evContainsAtom)
    

subsection "counterModel: lemmas"
  
lemma counterModelInRepn: "(counterM f,counterEvalP f) \<in> model"
  by (simp add: model_def counterM_def) 

lemmas Abs_counterModel_inverse = counterModelInRepn[THEN Abs_model_inverse]

lemma inv_obj_obj: "inv obj (obj n) = n"
  using inj_obj by  simp 

lemma map_X_map_counterAssign [simp]: "map X (map (inv obj) (map counterAssign xs)) = xs"
proof -
  have "(X \<circ> (inv obj \<circ> counterAssign)) = (\<lambda>x . x)"
    by (metis X_deX comp_apply counterAssign.simps inv_obj_obj)
  then show ?thesis
    by simp
qed
      
lemma objectsCounterModel: "objects (counterModel f) =  { z . \<exists>i . z = obj i }"
  unfolding objects_def counterModel_def Abs_counterModel_inverse
  by(force simp add: counterM_def) 

lemma inCounterM: "counterAssign v \<in> objects (counterModel f)"
  by (induction v) (force simp add: objectsCounterModel)

lemma evalPCounterModel: "M = counterModel f \<Longrightarrow> evalP M = counterEvalP f"
  by (simp add: evalP_def counterModel_def Abs_counterModel_inverse) 


subsection "counterModel: all path formula value false - step by step"

lemma path_evalF: 
assumes "branch subs (pseq fs) f" "\<And>n. \<not> proofTree (tree subs (f n))"
  shows "(\<exists>i . EV (contains f (i,A))) \<Longrightarrow> \<not> evalF (counterModel f) counterAssign A"
proof (induction A rule: measure_induct_rule [where f = size])
  case (less A)
  show ?case
    using less
  proof (induction A rule: formula_signs_induct)
    case (FAtomP p vs)
    with assms show ?case
      apply (simp add: evalPCounterModel counterEvalP_def list.map_comp)
      by (metis list.map_comp map_X_map_counterAssign)
  next
    case (FAtomN p vs)
    with assms show ?case
      apply (simp add: evalPCounterModel counterEvalP_def list.map_comp)
      by (metis list.map_comp map_X_map_counterAssign notEvContainsBothAtoms)
  next
    case (FConjP A B)
    with assms show ?case
      apply (simp add: evalPCounterModel counterEvalP_def list.map_comp)
      by (meson evContainsConj less_add_Suc1 less_add_Suc2)
  next
    case (FConjN A B)
    with assms show ?case
      apply (clarsimp simp add: evalPCounterModel counterEvalP_def list.map_comp)
      using evContainsDisj less_add_Suc1 less_add_Suc2 by blast
  next
    case (FAllP A)
    with assms obtain v where "EV (contains f (0, instanceF v A))"
      using evContainsAll by blast
    with FAllP.prems show ?case
      by (metis evalF_FAll evalF_instance inCounterM size_instance
          sizelemmas(3))
  next
    case (FAllN A)
    then obtain i where "\<not> evalF (counterModel f) counterAssign
            (instanceF (X i) A)"
      by (metis assms evContainsExval size_instance sizelemmas(3))
    with assms show ?case
      by (smt (verit, best) FAllN.prems counterAssign.simps evContainsExval evalF_FEx
          evalF_instance mem_Collect_eq objectsCounterModel size_instance
          sizelemmas(3))
  qed
qed


subsection "adequacy"

lemma counterAssignModelAssign: "counterAssign \<in> modelAssigns (counterModel \<gamma>)"
  by (simp add: inCounterM subset_eq)

lemma branch_contains_initially: "branch subs (pseq fs) f \<Longrightarrow> x \<in> set fs \<Longrightarrow> contains f (0,x) 0"
  by (simp add: contains_def branch0 pseq_def)

lemma validProofTree: 
  assumes "\<not> proofTree (tree subs (pseq fs))"
  shows "\<not> validS fs"
proof -
  obtain f where f: "branch subs (pseq fs) f" "\<And>n. \<not> proofTree (tree subs (f n))"
    by (metis assms failingBranchExistence fansSubs inheritedProofTree)
  then show ?thesis
    by (metis EV_def branch_contains_initially counterAssignModelAssign evalS_def
        path_evalF validS_def)
qed

theorem adequacy[simplified sequent_pseq]: "validS fs \<Longrightarrow> (sequent (pseq fs)) \<in> deductions CutFreePC"
  using proofTreeDeductionD validProofTree by blast

end
