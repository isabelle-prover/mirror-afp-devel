section \<open> Expression Test Cases and Examples \<close>

theory Expressions_Tests
  imports Expressions Named_Expressions
begin

text \<open> Some examples of lifted expressions follow. For now, we turn off the pretty printer so that 
  we can see the results of the parser.\<close>

declare [[pretty_print_exprs=false]]

term "(f + g)\<^sub>e" \<comment> \<open> Lift an expression and insert @{const SEXP} for pretty printing \<close>
term "(f + g)\<^sup>e" \<comment> \<open> Lift an expression and don't insert @{const SEXP} \<close>

text \<open> The default behaviour of our parser is to recognise identifiers as expression variables.
  So, the above expression becomes the term @{term "[\<lambda>\<s>. f \<s> + g \<s>]\<^sub>e"}. We can easily change
  this using the attribute @{attribute literal_variables}: \<close>

declare [[literal_variables]]

term "(f + g)\<^sub>e"

text \<open> Now, @{term f} and @{term g} are both parsed as literals, and so the term is 
  @{term "[\<lambda>\<s>. f + g]\<^sub>e"}. Alternatively, we could have a lens in the expression, by marking
  a free variable with a dollar : \<close>

term "($x + g)\<^sub>e"

text \<open> This gives the term @{term "[\<lambda>\<s>. get\<^bsub>x\<^esub> \<s> + g]\<^sub>e"}. Although we have default behaviours
  for parsing, we can use different markup to coerce identifiers to particular variable kinds. \<close>

term "($x + @g)\<^sub>e"

text \<open> This gives @{term "[\<lambda>\<s>. get\<^bsub>x\<^esub> \<s> + g \<s>]\<^sub>e"}, the we have requested that @{term "g"} is 
  treated as an expression variable. We can do similar with literal, as show below. \<close>

term "(f + \<guillemotleft>x\<guillemotright>)\<^sub>e"

text \<open> Some further examples follow. \<close>

term "(\<guillemotleft>f\<guillemotright> (@e))\<^sub>e"

term "(@f + @g)\<^sub>e"

term "(@x)\<^sub>e"

term "($x:y:z)\<^sub>e"

term "(($x:y):z)\<^sub>e"

term "(x::nat)\<^sub>e"

term "(\<forall> x::nat. x > 2)\<^sub>e"

term "SEXP(\<lambda> \<s>. get\<^bsub>x\<^esub> \<s> + e \<s> + v)"

term "(v \<in> $xs \<union> ($f) ys \<union> {} \<and> @e)\<^sub>e"

text \<open> We now turn pretty printing back on, so we can see how the user sees expressions. \<close>

declare [[pretty_print_exprs, literal_variables=false]]

term "($x\<^sup>< = $x\<^sup>>)\<^sub>e"

term "($x.1 = $y.2)\<^sub>e"

text \<open> The pretty printer works even when we don't use the parser, as shown below. \<close>

term "[\<lambda> \<s>. get\<^bsub>x\<^esub> \<s> + e \<s> + v]\<^sub>e"

text \<open> By default, dollars are printed next to free variables that are lenses. However, we can
  alter this behaviour with the attribute @{attribute mark_state_variables}: \<close>

declare [[mark_state_variables=false]]

term "($x + e + v)\<^sub>e"

text \<open> This way, the @{term "x"} variable is indistinguishable when printed from the @{term "e"}
  and @{term "v"}. Usually, this information can be inferred from the types of the entities: \<close>

alphabet st = 
  x :: int

term "(x + e + v)\<^sub>e"

expression x_is_big over st is "x > 1000"

term "(x_is_big \<longrightarrow> x > 0)\<^sub>e"

text \<open> Here, @{term x} is a lens defined by the @{command alphabet} command, and so the lifting
  translation treats it as a state variable. This is hidden from the user. \<close>

dataspace testspace =
   variables z :: int

declare [[literal_variables]]

context testspace
begin

edefinition "z_is_bigger y = (z > y)"

term "(z_is_bigger (z + 1))\<^sub>e"

end

end