chapter \<open>The prover\<close>

section \<open>Proof search procedure\<close>

theory Prover
  imports SeCaV
    "HOL-Library.Stream"
    Abstract_Completeness.Abstract_Completeness
    Abstract_Soundness.Finite_Proof_Soundness
    "HOL-Library.Countable"
    "HOL-Library.Code_Lazy"
begin

text \<open>This theory defines the actual proof search procedure.\<close>

subsection \<open>Datatypes\<close>

text \<open>A sequent is a list of formulas\<close>
type_synonym sequent = \<open>fm list\<close>

text \<open>We introduce a number of rules to prove sequents.
  These rules mirror the proof system of SeCaV, but are higher-level in the sense that they apply to
  all formulas in the sequent at once. This obviates the need for the structural Ext rule.
  There is also no Basic rule, since this is implicit in the prover.\<close>
datatype rule
  = AlphaDis | AlphaImp  | AlphaCon
  | BetaCon | BetaImp | BetaDis
  | DeltaUni | DeltaExi
  | NegNeg
  | GammaExi | GammaUni

subsection \<open>Auxiliary functions\<close>

text \<open>Before defining what the rules do, we need to define a number of auxiliary functions needed
  for the semantics of the rules.\<close>

text \<open>listFunTm is a list of function and constant names in a term\<close>
primrec listFunTm :: \<open>tm \<Rightarrow> nat list\<close> and listFunTms :: \<open>tm list \<Rightarrow> nat list\<close>where
  \<open>listFunTm (Fun n ts) = n # listFunTms ts\<close>
| \<open>listFunTm (Var n) = []\<close>
| \<open>listFunTms [] = []\<close>
| \<open>listFunTms (t # ts) = listFunTm t @ listFunTms ts\<close>

text \<open>generateNew uses the \<open>listFunTms\<close> function to obtain a fresh function index\<close>
definition generateNew :: \<open>tm list \<Rightarrow> nat\<close> where
  \<open>generateNew ts \<equiv> 1 + foldr max (listFunTms ts) 0\<close>

text \<open>subtermTm returns a list of all terms occurring within a term\<close>
primrec subtermTm :: \<open>tm \<Rightarrow> tm list\<close> where
  \<open>subtermTm (Fun n ts) = Fun n ts # remdups (concat (map subtermTm ts))\<close>
| \<open>subtermTm (Var n) = [Var n]\<close>

text \<open>subtermFm returns a list of all terms occurring within a formula\<close>
primrec subtermFm :: \<open>fm \<Rightarrow> tm list\<close> where
  \<open>subtermFm (Pre _ ts) = concat (map subtermTm ts)\<close>
| \<open>subtermFm (Imp p q) = subtermFm p @ subtermFm q\<close>
| \<open>subtermFm (Dis p q) = subtermFm p @ subtermFm q\<close>
| \<open>subtermFm (Con p q) = subtermFm p @ subtermFm q\<close>
| \<open>subtermFm (Exi p) = subtermFm p\<close>
| \<open>subtermFm (Uni p) = subtermFm p\<close>
| \<open>subtermFm (Neg p) = subtermFm p\<close>

text \<open>subtermFms returns a list of all terms occurring within a list of formulas\<close>
abbreviation \<open>subtermFms z \<equiv> concat (map subtermFm z)\<close>

text \<open>subterms returns a list of all terms occurring within a sequent.
  This is used to determine which terms to instantiate Gamma-formulas with.
  We must always be able to instantiate Gamma-formulas, so if there are no terms in the sequent,
  the function simply returns a list containing the first function.\<close>
definition subterms :: \<open>sequent \<Rightarrow> tm list\<close> where
  \<open>subterms z \<equiv> case remdups (subtermFms z) of
                [] \<Rightarrow> [Fun 0 []]
              | ts \<Rightarrow> ts\<close>

text \<open>We need to be able to detect if a sequent is an axiom to know whether a branch of the proof
  is done. The disjunct \<open>Neg (Neg p) \<in> set z\<close> is not necessary for the prover, but makes the proof
  of the lemma \<open>branchDone_contradiction\<close> easier.\<close>
fun branchDone :: \<open>sequent \<Rightarrow> bool\<close> where
  \<open>branchDone [] = False\<close>
| \<open>branchDone (Neg p # z) = (p \<in> set z \<or> Neg (Neg p) \<in> set z \<or> branchDone z)\<close>
| \<open>branchDone (p # z) = (Neg p \<in> set z \<or> branchDone z)\<close>

subsection \<open>Effects of rules\<close>

text \<open>This defines the resulting formulas when applying a rule to a single formula.
  This definition mirrors the semantics of SeCaV.
  If the rule and the formula do not match, the resulting formula is simply the original formula.
  Parameter A should be the list of terms on the branch.\<close>
definition parts :: \<open>tm list \<Rightarrow> rule \<Rightarrow> fm \<Rightarrow> fm list list\<close> where
  \<open>parts A r f = (case (r, f) of
      (NegNeg, Neg (Neg p)) \<Rightarrow> [[p]]
    | (AlphaImp, Imp p q) \<Rightarrow> [[Neg p, q]]
    | (AlphaDis, Dis p q) \<Rightarrow> [[p, q]]
    | (AlphaCon, Neg (Con p q)) \<Rightarrow> [[Neg p, Neg q]]
    | (BetaImp, Neg (Imp p q)) \<Rightarrow> [[p], [Neg q]]
    | (BetaDis, Neg (Dis p q)) \<Rightarrow> [[Neg p], [Neg q]]
    | (BetaCon, Con p q) \<Rightarrow> [[p], [q]]
    | (DeltaExi, Neg (Exi p)) \<Rightarrow> [[Neg (sub 0 (Fun (generateNew A) []) p)]]
    | (DeltaUni, Uni p) \<Rightarrow> [[sub 0 (Fun (generateNew A) []) p]]
    | (GammaExi, Exi p) \<Rightarrow> [Exi p # map (\<lambda>t. sub 0 t p) A]
    | (GammaUni, Neg (Uni p)) \<Rightarrow> [Neg (Uni p) # map (\<lambda>t. Neg (sub 0 t p)) A]
    | _ \<Rightarrow> [[f]])\<close>

text \<open>This function defines the Cartesian product of two lists.
  This is needed to create the list of branches created when applying a beta rule.\<close>
primrec list_prod :: \<open>'a list list \<Rightarrow> 'a list list \<Rightarrow> 'a list list\<close> where
  \<open>list_prod _ [] = []\<close>
| \<open>list_prod hs (t # ts) = map (\<lambda>h. h @ t) hs @ list_prod hs ts\<close>

text \<open>This function computes the children of a node in the proof tree.
  For Alpha rules, Delta rules and Gamma rules, there will be only one sequent, which is the result
  of applying the rule to every formula in the current sequent.
  For Beta rules, the proof tree will branch into two branches once for each formula in the sequent
  that matches the rule, which results in \<open>2\<^sup>n\<close> branches (created using \<^text>\<open>list_prod\<close>).
  The list of terms in the sequent needs to be updated after applying the rule to each formula since
  Delta rules and Gamma rules may introduce new terms.
  Note that any formulas that don't match the rule are left unchanged in the new sequent.\<close>
primrec children :: \<open>tm list \<Rightarrow> rule \<Rightarrow> sequent \<Rightarrow> sequent list\<close> where
  \<open>children _ _ [] = [[]]\<close>
| \<open>children A r (p # z) =
  (let hs = parts A r p; A' = remdups (A @ subtermFms (concat hs))
   in list_prod hs (children A' r z))\<close>

text \<open>The proof state is the combination of a list of terms and a sequent.\<close>
type_synonym state = \<open>tm list \<times> sequent\<close>

text \<open>This function defines the effect of applying a rule to a proof state.
  If the sequent is an axiom, the effect is to end the branch of the proof tree, so an empty set of
  child branches is returned.
  Otherwise, we compute the children generated by applying the rule to the current proof state,
  then add any new subterms to the proof states of the children.\<close>
primrec effect :: \<open>rule \<Rightarrow> state \<Rightarrow> state fset\<close> where
  \<open>effect r (A, z) =
  (if branchDone z then {||} else
    fimage (\<lambda>z'. (remdups (A @ subterms z @ subterms z'), z'))
    (fset_of_list (children (remdups (A @ subtermFms z)) r z)))\<close>

subsection \<open>The rule stream\<close>

text \<open>We need to define an infinite stream of rules that the prover should try to apply.
  Since rules simply do nothing if they don't fit the formulas in the sequent, the rule stream is
  just all rules in the order: Alpha, Delta, Beta, Gamma, which guarantees completeness.\<close>
definition \<open>rulesList \<equiv> [
  NegNeg, AlphaImp, AlphaDis, AlphaCon,
  DeltaExi, DeltaUni,
  BetaImp, BetaDis, BetaCon,
  GammaExi, GammaUni
]\<close>

text \<open>By cycling the list of all rules we obtain an infinite stream with every rule occurring
  infinitely often.\<close>
definition rules where
  \<open>rules = cycle rulesList\<close>

subsection \<open>Abstract completeness\<close>

text \<open>We write effect as a relation to use it with the abstract completeness framework.\<close>
definition eff where
  \<open>eff \<equiv> \<lambda>r s ss. effect r s = ss\<close>

text \<open>To use the framework, we need to prove enabledness.
  This is trivial because all of our rules are always enabled and simply do nothing if they don't
  match the formulas.\<close>
lemma all_rules_enabled: \<open>\<forall>st. \<forall>r \<in> i.R (cycle rulesList). \<exists>sl. eff r st sl\<close>
  unfolding eff_def by blast

text \<open>The first step of the framework is to prove that our prover fits the framework.\<close>
interpretation RuleSystem eff rules UNIV
  unfolding rules_def RuleSystem_def
  using all_rules_enabled stream.set_sel(1)
  by blast

text \<open>Next, we need to prove that our rules are persistent.
  This is also trivial, since all of our rules are always enabled.\<close>
lemma all_rules_persistent: \<open>\<forall>r. r \<in> R \<longrightarrow> per r\<close>
  by (metis all_rules_enabled enabled_def per_def rules_def)

text \<open>We can then prove that our prover fully fits the framework.\<close>
interpretation PersistentRuleSystem eff rules UNIV
  unfolding PersistentRuleSystem_def RuleSystem_def PersistentRuleSystem_axioms_def
  using all_rules_persistent enabled_R
  by blast

text \<open>We can then use the framework to define the prover.
  The mkTree function applies the rules to build the proof tree using the effect relation, but the
  prover is not actually executable yet.\<close>
definition \<open>secavProver \<equiv> mkTree rules\<close>

abbreviation \<open>rootSequent t \<equiv> snd (fst (root t))\<close>

end
