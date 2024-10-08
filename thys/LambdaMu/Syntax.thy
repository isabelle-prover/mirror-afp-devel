section \<open>The $\lambda\mu$-calculus\<close>

text\<open>More examples, as well as a call-by-value programming language built on
top of our formalisation, can be found in an associated Bitbucket repository~\<^cite>\<open>"bitbucket"\<close>.\<close>
  
theory Syntax
  imports Main
begin

subsection \<open>Syntax\<close>

datatype type = 
     Iota
    | Fun type type (infixr \<open>\<rightarrow>\<close> 200)

text\<open>To deal with $\alpha$-equivalence, we use De Bruijn's nameless representation wherein each bound
     variable is represented by a natural number, its index, that denotes the number of binders
     that must be traversed to arrive at the one that binds the given variable.
     Each free variable has an index that points into the top-level context, not enclosed in
     any abstractions.\<close>
  
datatype trm =
      LVar nat    (\<open>`_\<close> [100] 100)
    | Lbd type trm (\<open>\<lambda>_:_\<close> [0, 60] 60)
    | App trm trm (infix \<open>\<degree>\<close> 60)
    | Mu type cmd (\<open>\<mu>_:_\<close> [0, 60] 60)
and cmd = 
      MVar nat trm (\<open><_>_\<close> [0, 60] 60)
      
datatype ctxt = 
  ContextEmpty (\<open>\<diamond>\<close>) |
  ContextApp ctxt trm (infixl \<open>\<^sup>\<bullet>\<close> 75)
  
primrec ctxt_app :: "ctxt \<Rightarrow> ctxt \<Rightarrow> ctxt" (infix \<open>.\<close> 60) where
  "\<diamond> . F = F" |
  "(E \<^sup>\<bullet> t) . F = (E . F) \<^sup>\<bullet> t"
  
fun is_val :: "trm \<Rightarrow> bool" where
  "is_val (\<lambda> T : v) = True" |
  "is_val _ = False"

  
end
