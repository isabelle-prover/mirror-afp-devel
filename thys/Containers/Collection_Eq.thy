(*  Title:      Containers/Collection_Eq.thy
    Author:     Andreas Lochbihler, KIT
                René Thiemann, UIBK *)
theory Collection_Eq imports
  Auxiliary
  Containers_Generator
begin

section {* A type class for optional equality testing *}

class ceq =
  fixes ceq :: "('a \<Rightarrow> 'a \<Rightarrow> bool) option"
  assumes ceq: "ceq = Some eq \<Longrightarrow> eq = op ="
begin

lemma ID_ceq: "ID ceq = Some eq \<Longrightarrow> eq = op ="
unfolding ID_def id_apply by(rule ceq)

abbreviation ceq' :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where "ceq' \<equiv> the (ID ceq)"

end

syntax "_CEQ" :: "type => logic"  ("(1CEQ/(1'(_')))")

parse_translation {*
let
  fun ceq_tr [ty] =
     (Syntax.const @{syntax_const "_constrain"} $ Syntax.const @{const_syntax "ceq"} $
       (Syntax.const @{type_syntax option} $ 
         (Syntax.const @{type_syntax fun} $ ty $ 
           (Syntax.const @{type_syntax fun} $ ty $ Syntax.const @{type_syntax bool}))))
    | ceq_tr ts = raise TERM ("ceq_tr", ts);
in [(@{syntax_const "_CEQ"}, K ceq_tr)] end
*}

typed_print_translation {*
let
  fun ceq_tr' ctxt
    (Type (@{type_name option}, [Type (@{type_name fun}, [T, _])])) ts =
    Term.list_comb (Syntax.const @{syntax_const "_CEQ"} $ Syntax_Phases.term_of_typ ctxt T, ts)
  | ceq_tr' _ _ _ = raise Match;
in [(@{const_syntax ceq}, ceq_tr')]
end
*}

definition is_ceq :: "'a :: ceq itself \<Rightarrow> bool"
where "is_ceq _ \<longleftrightarrow> ID CEQ('a) \<noteq> None"

subsection {* Generator for the @{class ceq}-class *}

text {*
This generator registers itself at the derive-manager for the class @{class ceq}.
To be more precise, one can choose whether one wants to take @{term "op ="} as function
for @{term ceq} by passing "eq" as parameter, 
whether equality should not be supported by passing "no" as parameter,
or whether an own definition for equality should be derived by not passing
any parameters. The last possibility only works for datatypes.

\begin{itemize}
\item \texttt{instantiation type :: (type,\ldots,type) (eq) ceq}
\item \texttt{instantiation type :: (type,\ldots,type) (no) ceq}
\item \texttt{instantiation datatype :: (ceq,\ldots,ceq) ceq}
\end{itemize}

If the parameter "no" is not used, then the corresponding
@{term is_ceq}-theorem is also automatically generated and attributed with 
\texttt{[simp, code-post]}.
*}


text {*
This generator can be used for arbitrary types, not just datatypes. 
*}

ML_file "ceq_generator.ML"

setup {*
  Ceq_Generator.setup
*}

subsection {* Type class instances for HOL types *}

derive (eq) ceq unit
lemma [code]: "CEQ(unit) = Some (\<lambda>_ _. True)"
  unfolding ceq_unit_def by (simp, intro ext, auto)
derive (eq) ceq bool
derive (eq) ceq nat
derive (eq) ceq int
derive (eq) ceq Enum.finite_1
derive (eq) ceq Enum.finite_2
derive (eq) ceq Enum.finite_3
derive (eq) ceq Enum.finite_4
derive (eq) ceq Enum.finite_5
derive (eq) ceq integer
derive (eq) ceq natural
derive (eq) ceq nibble
derive (eq) ceq char
derive (eq) ceq String.literal
derive ceq sum
derive ceq prod
derive ceq list
derive ceq option
derive (no) ceq "fun"

lemma is_ceq_fun [simp]: "\<not> is_ceq TYPE('a \<Rightarrow> 'b)"
  by(simp add: is_ceq_def ceq_fun_def ID_None) 

definition set_eq :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" 
where [code del]: "set_eq = op ="

lemma set_eq_code:
  shows [code]: "set_eq A B \<longleftrightarrow> A \<subseteq> B \<and> B \<subseteq> A"
  and [code_unfold]: "op = = set_eq"
unfolding set_eq_def by blast+

instantiation set :: (ceq) ceq begin
definition "CEQ('a set) = (case ID CEQ('a) of None \<Rightarrow> None | Some _ \<Rightarrow> Some set_eq)"
instance by(intro_classes)(simp add: ceq_set_def set_eq_def split: option.splits)
end

lemma is_ceq_set [simp, code_post]: "is_ceq TYPE('a set) \<longleftrightarrow> is_ceq TYPE('a :: ceq)"
by(simp add: is_ceq_def ceq_set_def ID_None ID_Some split: option.split)

lemma ID_ceq_set_not_None_iff [simp]: "ID CEQ('a set) \<noteq> None \<longleftrightarrow> ID CEQ('a :: ceq) \<noteq> None"
by(simp add: ceq_set_def ID_def split: option.splits)

end
