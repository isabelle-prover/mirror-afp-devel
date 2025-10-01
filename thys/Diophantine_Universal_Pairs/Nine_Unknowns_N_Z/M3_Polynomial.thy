theory M3_Polynomial
  imports Pi_Relations Polynomials.MPoly_Type_Univariate
          "../MPoly_Utils/Poly_Extract" "../MPoly_Utils/Poly_Degree"
begin

subsection \<open>The Matiyasevich-Robinson-Polynomial\<close>

text \<open>For any appropriately typed function fn, we introduce the syntax
        \<open>fn \<pi> \<equiv> fn A1 A2 A3 S T R n\<close>, as well as \<open>(\<lambda>\<pi>. e) \<equiv> (\<lambda>A1 A2 A3 S T R n. e)\<close>.\<close>

syntax "pi" :: "(int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> int" ("_ \<pi>" [1000] 1000)
syntax "pi_fn" :: "(int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> int" ("\<lambda>\<pi>. _" [0] 0)
parse_translation \<open>
  [
    (
      \<^syntax_const>\<open>pi\<close>,
      fn ctxt => fn args =>
        list_comb (
          args |> hd,
          ["A\<^sub>1", "A\<^sub>2", "A\<^sub>3", "S", "T", "R", "n"] |> map (fn name => Free (name, @{typ int}))
        )
    ),
    (
      \<^syntax_const>\<open>pi_fn\<close>,
      fn ctxt => fn args =>
        ["A\<^sub>1", "A\<^sub>2", "A\<^sub>3", "S", "T", "R", "n"]
          |> List.foldr (fn (name, r) => Abs (name, @{typ int}, r)) (args |> hd)
    )
  ]
\<close>

locale section5 = section5_given + section5_variables
begin

definition X\<^sub>0 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "X\<^sub>0 \<pi> = 1 + A\<^sub>1^2 + A\<^sub>2^2 + A\<^sub>3^2"
definition I\<^sub>0 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "I\<^sub>0 \<pi> = (X\<^sub>0 \<pi>)^3"
definition U\<^sub>0 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "U\<^sub>0 \<pi> = S^2 * (2 * R - 1)"
definition V\<^sub>0 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "V\<^sub>0 \<pi> = S^2 * n + T^2"

poly_extract X\<^sub>0
poly_extract I\<^sub>0
poly_extract U\<^sub>0
poly_extract V\<^sub>0


definition M3 :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "M3 A\<^sub>1 A\<^sub>2 A\<^sub>3 S T R n =
    (
      ((
        (
          (
            ((V\<^sub>0 \<pi>) - (U\<^sub>0 \<pi>) * (I\<^sub>0 \<pi>) - (U\<^sub>0 \<pi>) * T^2)^2
              + (U\<^sub>0 \<pi>)^2 * A\<^sub>1
              + (U\<^sub>0 \<pi>)^2 * A\<^sub>2 * (X\<^sub>0 \<pi>)^2
              - (U\<^sub>0 \<pi>)^2 * A\<^sub>3 * (X\<^sub>0 \<pi>)^4
          )
        )^2 
          + 4 * (U\<^sub>0 \<pi>)^2 * (V\<^sub>0 \<pi> - U\<^sub>0 \<pi> * I\<^sub>0 \<pi> - U\<^sub>0 \<pi> * T^2)^2 * A\<^sub>1
          - 4 * (U\<^sub>0 \<pi>)^2 * (V\<^sub>0 \<pi> - U\<^sub>0 \<pi> * I\<^sub>0 \<pi> - U\<^sub>0 \<pi> * T^2)^2 * A\<^sub>2 * (X\<^sub>0 \<pi>)^2
          - 4 * (U\<^sub>0 \<pi>)^4 * A\<^sub>1 * A\<^sub>2 * (X\<^sub>0 \<pi>)^2
      )^2)
        - A\<^sub>1 * (U\<^sub>0 \<pi> * (
          4
            * (V\<^sub>0 \<pi> - U\<^sub>0 \<pi> * I\<^sub>0 \<pi> - U\<^sub>0 \<pi> * T^2)
            * (
              ((V\<^sub>0 \<pi> - U\<^sub>0 \<pi> * I\<^sub>0 \<pi> - U\<^sub>0 \<pi> * T^2))^2
                + (U\<^sub>0 \<pi>)^2 * A\<^sub>1
                + (U\<^sub>0 \<pi>)^2 * A\<^sub>2 * (X\<^sub>0 \<pi>)^2
                - (U\<^sub>0 \<pi>)^2 * A\<^sub>3 * (X\<^sub>0 \<pi>)^4
              )
                - 8
                  * (U\<^sub>0 \<pi>)^2
                  * (V\<^sub>0 \<pi> - U\<^sub>0 \<pi> * I\<^sub>0 \<pi> - U\<^sub>0 \<pi> * T^2)
                  * A\<^sub>2
                  * (X\<^sub>0 \<pi>)^2
        ))^2
    )
"

poly_extract M3

end

end
