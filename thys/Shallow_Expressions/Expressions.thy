section \<open> Expressions \<close>

theory Expressions
  imports Variables
  keywords "expr_constructor" "expr_function" :: "thy_decl_block"
begin

subsection \<open> Types and Constructs \<close>

named_theorems expr_defs and named_expr_defs

text \<open> An expression is represented simply as a function from the state space @{typ "'s"} to
  the return type @{typ "'a"}, which is the simplest shallow model for Isabelle/HOL. 

  The aim of this theory is to provide transparent conversion between this representation 
  and a more intuitive expression syntax. For example, an expression @{term "x + y"} where 
  $x$ and $y$ are both state variables, can be represented by @{term "\<lambda> s. get\<^bsub>x\<^esub> s + get\<^bsub>y\<^esub> s"} 
  when both variables are modelled using lenses. Rather than having to write $\lambda$-terms 
  directly, it is more convenient to hide this threading of state behind a parser. We introduce
  the expression bracket syntax, @{text "(_)\<^sub>e"} to support this.
\<close>

type_synonym ('a, 's) expr = "'s \<Rightarrow> 'a"

text \<open> The following constructor is used to syntactically mark functions that actually
  denote expressions. It is semantically vacuous. \<close>

definition SEXP :: "('s \<Rightarrow> 'a) \<Rightarrow> ('a, 's) expr" ("[_]\<^sub>e") where
[expr_defs]: "SEXP x = x"

lemma SEXP_apply [simp]: "SEXP e s = (e s)" by (simp add: SEXP_def)

lemma SEXP_idem [simp]: "[[e]\<^sub>e]\<^sub>e = [e]\<^sub>e" by (simp add: SEXP_def)

text \<open> We can create the core constructs of a simple expression language as indicated below. \<close>

abbreviation (input) var :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) expr" where
"var x \<equiv> (\<lambda> s. get\<^bsub>x\<^esub> s)"

abbreviation (input) lit :: "'a \<Rightarrow> ('a, 's) expr" where
"lit k \<equiv> (\<lambda> s. k)"

abbreviation (input) uop :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 's) expr \<Rightarrow> ('b, 's) expr" where
"uop f e \<equiv> (\<lambda> s. f (e s))"

abbreviation (input) bop 
  :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, 's) expr \<Rightarrow> ('b, 's) expr \<Rightarrow> ('c, 's) expr" where
"bop f e\<^sub>1 e\<^sub>2 \<equiv> (\<lambda> s. f (e\<^sub>1 s) (e\<^sub>2 s))"

definition taut :: "(bool, 's) expr \<Rightarrow> bool" where
[expr_defs]: "taut e = (\<forall> s. e s)"

definition expr_select :: "('a, 's) expr \<Rightarrow> ('b \<Longrightarrow> 'a) \<Rightarrow> ('b, 's) expr" where
[expr_defs, code_unfold]: "expr_select e x = (\<lambda> s. get\<^bsub>x\<^esub> (e s))"

definition expr_if :: "('a, 's) expr \<Rightarrow> (bool, 's) expr \<Rightarrow> ('a, 's) expr \<Rightarrow> ('a, 's) expr" where
[expr_defs, code_unfold]: "expr_if P b Q = (\<lambda> s. if (b s) then P s else Q s)"

subsection \<open> Lifting Parser and Printer \<close>

text \<open> The lifting parser creates a parser directive that converts an expression to a 
  @{const SEXP} boxed $\lambda$-term that gives it a semantics. A pretty printer converts
  a boxed $\lambda$-term back to an expression. \<close>

nonterminal sexp

text \<open> We create some syntactic constants and define parse and print translations for them. \<close>

syntax
  "_sexp_state"      :: "id"
  "_sexp_quote"      :: "logic \<Rightarrow> logic" ("'(_')\<^sub>e")
  \<comment> \<open> Convert the expression to a lambda term, but do not box it. \<close>
  "_sexp_quote_1way" :: "logic \<Rightarrow> logic" ("'(_')\<^sup>e")
  "_sexp_lit"        :: "logic \<Rightarrow> logic" ("\<guillemotleft>_\<guillemotright>")
  "_sexp_var"        :: "svid \<Rightarrow> logic" ("$_" [990] 990)
  "_sexp_evar"       :: "id_position \<Rightarrow> logic" ("@_" [999] 999)
  "_sexp_evar"       :: "logic \<Rightarrow> logic" ("@'(_')" [999] 999)
  "_sexp_pqt"        :: "logic \<Rightarrow> sexp" ("[_]\<^sub>e")
  "_sexp_taut"       :: "logic \<Rightarrow> logic" ("`_`")
  "_sexp_select"     :: "logic \<Rightarrow> svid \<Rightarrow> logic" ("_:_" [1000, 999] 1000)
  "_sexp_if"         :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3_ \<triangleleft> _ \<triangleright>/ _)" [52,0,53] 52)

ML_file \<open>Lift_Expr.ML\<close>

text \<open> We create a number of attributes for configuring the way the parser works. \<close> 

declare [[pretty_print_exprs=true]]


text \<open> We can toggle pretty printing of $\lambda$ expressions using @{attribute pretty_print_exprs}. \<close>

declare [[literal_variables=false]]

text \<open> Expressions, of course, can contain variables. However, a variable can denote one of
  three things: (1) a state variable (i.e. a lens); (2) a placeholder for a value (i.e. a
  HOL literal); and (3) a placeholder for another expression. The attribute @{attribute literal_variables}
  selects option (2) as the default behaviour when true, and option (3) when false. \<close>

expr_constructor expr_select
expr_constructor expr_if

text \<open> Some constants should not be lifted, since they are effectively constructors for expressions.
  The command @{command expr_constructor} allows us to specify such constants to not be lifted.
  This being the case, the arguments are left unlifted, unless included in a list of numbers
  before the constant name. The state is passed as the final argument to expression constructors.
\<close>

parse_translation \<open> 
  [(@{syntax_const "_sexp_state"}, fn ctx => fn term => Syntax.free Lift_Expr.state_id),
   (@{syntax_const "_sexp_quote"}
   , fn ctx => fn terms =>
      case terms of
        [Const (@{const_syntax SEXP}, t) $ e] => Const (@{const_name SEXP}, t) $ e |
        [e] =>
            Syntax.const @{const_name SEXP} $ Lift_Expr.mk_lift_expr ctx dummyT e),
   (@{syntax_const "_sexp_quote_1way"}
   , fn ctx => fn terms =>
      case terms of
        [e] => Lift_Expr.mk_lift_expr ctx dummyT e)]
\<close>

print_translation \<open>
  [(@{const_syntax "SEXP"}
   , fn ctx => fn ts =>
     if not (Config.get ctx Lift_Expr.pretty_print_exprs)
     then Term.list_comb (Syntax.const @{syntax_const "_sexp_pqt"}, ts)
     else
     Syntax.const @{syntax_const "_sexp_quote"} 
     $ Lift_Expr.print_expr ctx (betapply ((hd ts), Syntax.const @{syntax_const "_sexp_state"})))]
\<close>

translations
  "_sexp_var x" => "get\<^bsub>x\<^esub> _sexp_state"
  "_sexp_taut p" == "CONST taut (p)\<^sub>e"
  "_sexp_select e x" == "CONST expr_select (e)\<^sub>e x"
  "_sexp_if P b Q" == "CONST expr_if P (b)\<^sub>e Q"
  "_sexp_var (_svid_tuple (_of_svid_list (x +\<^sub>L y)))" <= "_sexp_var (x +\<^sub>L y)"

text \<open> The main directive is the $e$ subscripted brackets, @{term "(e)\<^sub>e"}. This converts the 
  expression $e$ to a boxed $\lambda$ term. Essentially, the behaviour is as follows:

  \begin{enumerate}
    \item a new $\lambda$ abstraction over the state variable $s$ is wrapped around $e$;
    \item every occurrence of a free lens @{term "$x"} in $e$ is replaced by @{term "get\<^bsub>x\<^esub> s"};
    \item every occurrence of an expression variable @{term "e"} is replaced by @{term "e s"};
    \item every occurrence of any other free variable is left unchanged.
  \end{enumerate}

  The pretty printer does this in reverse. \<close>

text \<open> Below is a grammar category for lifted expressions. \<close>

nonterminal sexpr

syntax "_sexpr" :: "logic \<Rightarrow> sexpr" ("_")

parse_translation \<open>
  [(@{syntax_const "_sexpr"}, fn ctx => fn [e] => 
    Syntax.const @{const_name SEXP} 
            $ (lambda (Syntax.free Lift_Expr.state_id) 
                      (Lift_Expr.lift_expr ctx dummyT (Term_Position.strip_positions e))))]
\<close>

subsection \<open> Reasoning \<close>

lemma expr_eq_iff: "P = Q \<longleftrightarrow> `P = Q`"
  by (simp add: taut_def fun_eq_iff)

lemma refine_iff_implies: "P \<le> Q \<longleftrightarrow> `P \<longrightarrow> Q`"
  by (simp add: le_fun_def taut_def)

lemma taut_True [simp]: "`True` = True"
  by (simp add: taut_def)

lemma taut_False [simp]: "`False` = False"
  by (simp add: taut_def)

lemma tautI: "\<lbrakk> \<And> s. P s \<rbrakk> \<Longrightarrow> taut P"
  by (simp add: taut_def)

named_theorems expr_simps

text \<open> Lemmas to help automation of expression reasoning \<close>

lemma fst_case_sum [simp]: "fst (case p of Inl x \<Rightarrow> (a1 x, a2 x) | Inr x \<Rightarrow> (b1 x, b2 x)) = (case p of Inl x \<Rightarrow> a1 x | Inr x \<Rightarrow> b1 x)"
  by (simp add: sum.case_eq_if)

lemma snd_case_sum [simp]: "snd (case p of Inl x \<Rightarrow> (a1 x, a2 x) | Inr x \<Rightarrow> (b1 x, b2 x)) = (case p of Inl x \<Rightarrow> a2 x | Inr x \<Rightarrow> b2 x)"
  by (simp add: sum.case_eq_if)

lemma sum_case_apply [simp]: "(case p of Inl x \<Rightarrow> f x | Inr x \<Rightarrow> g x) y = (case p of Inl x \<Rightarrow> f x y | Inr x \<Rightarrow> g x y)"
  by (simp add: sum.case_eq_if)

text \<open> Proof methods for simplifying shallow expressions to HOL terms. The first retains the lens
  structure, and the second removes it when alphabet lenses are present.  \<close>

method expr_lens_simp uses add = 
  ((simp add: expr_simps)? \<comment> \<open> Perform any possible simplifications retaining the lens structure \<close>
   ;((simp add: fun_eq_iff prod.case_eq_if expr_defs named_expr_defs lens_defs add)? ; \<comment> \<open> Explode the rest \<close>
     (simp add: expr_defs named_expr_defs lens_defs add)?))

method expr_simp uses add = (expr_lens_simp add: alpha_splits add)

text \<open> Methods for dealing with tautologies \<close>

method expr_lens_taut uses add = 
  (rule tautI;
   expr_lens_simp add: add)

method expr_taut uses add = 
  (rule tautI;
   expr_simp add: add; 
   rename_alpha_vars?)

text \<open> A method for simplifying shallow expressions to HOL terms and applying @{method auto} \<close>

method expr_auto uses add =
  (expr_simp add: add; 
   (auto simp add: alpha_splits lens_defs add)?; 
   (rename_alpha_vars)? \<comment> \<open> Rename any logical variables with v subscripts \<close>
  )

subsection \<open> Algebraic laws \<close>

lemma expr_if_idem [simp]: "P \<triangleleft> b \<triangleright> P = P"
  by expr_auto

lemma expr_if_sym: "P \<triangleleft> b \<triangleright> Q = Q \<triangleleft> \<not>b \<triangleright> P"
  by expr_auto

lemma expr_if_assoc: "(P \<triangleleft> b \<triangleright> Q) \<triangleleft> c \<triangleright> R = P \<triangleleft> b \<and> c \<triangleright> (Q \<triangleleft> c \<triangleright> R)"
  by expr_auto

lemma expr_if_distr: "P \<triangleleft> b \<triangleright> (Q \<triangleleft> c \<triangleright> R) = (P \<triangleleft> b \<triangleright> Q) \<triangleleft> c \<triangleright> (P \<triangleleft> b \<triangleright> R)"
  by expr_auto

lemma expr_if_true [simp]: "P \<triangleleft> True \<triangleright> Q = P"
  by expr_auto

lemma expr_if_false [simp]: "P \<triangleleft> False \<triangleright> Q = Q"
  by expr_auto

lemma expr_if_reach [simp]: "P \<triangleleft> b \<triangleright> (Q \<triangleleft> b \<triangleright> R) = P \<triangleleft> b \<triangleright> R"
  by expr_auto

lemma expr_if_disj [simp]: "P \<triangleleft> b \<triangleright> (P \<triangleleft> c \<triangleright> Q) = P \<triangleleft> b \<or> c \<triangleright> Q"
  by expr_auto

lemma SEXP_expr_if: "[expr_if P b Q]\<^sub>e = expr_if P b Q"
  by (simp add: SEXP_def)

end