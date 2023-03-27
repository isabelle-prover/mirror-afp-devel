(*
   Mike Stannett
   Feb 2023
*)

section \<open> AXIOM: AxLightMinus \<close>

text \<open>This theory declares the axiom AxLightMinus.\<close>

theory AxLightMinus
  imports WorldLine TangentLines
begin

text \<open>AxLightMinus:
   If an observer sends out a light signal, then the speed of the 
   light signal is 1 according to the observer. Moreover it is possible to send
   out a light signal in any direction.\<close>

(*
   (\<forall>m \<in> Ob)(\<forall>p \<in> wline_m(m)(\<forall>v in Q3)
      (\<exists>ph \<in> Ph)vel_m(ph,p) = v  \<longleftrightarrow>  |v| = 1

  Given the new definition of velocity, we need to define the worldline
of ph according to m, i.e.

  wl_m(ph) = { q :  m sees ph at q }
           = \<lambda> q . m sees ph at q
*)

class axLightMinus = WorldLine + TangentLines
begin

text \<open>The definition of AxLightMinus used in this Isabelle proof is slightly
different to the one used in the paper-based proof on which it is based. We
have established elsewhere, however, that each entails the other in all
relevant contexts.\<close>

abbreviation axLightMinusOLD :: "Body \<Rightarrow> 'a Point \<Rightarrow> 'a Space \<Rightarrow> bool" 
  where "axLightMinusOLD m p v \<equiv> (m sees m at p) \<longrightarrow> ( 
     (\<exists> ph . (Ph ph \<and> (vel (wline m ph) p v)))  \<longleftrightarrow>  (sNorm2 v = 1)
   )"

abbreviation axLightMinus :: "Body \<Rightarrow> 'a Point \<Rightarrow> 'a Space \<Rightarrow> bool" 
  where "axLightMinus m p v \<equiv> (m sees m at p) 
         \<longrightarrow> ( \<forall> l . \<forall> v \<in> lineVelocity l .
                (\<exists> ph . (Ph ph \<and> (tangentLine l (wline m ph) p)))  \<longleftrightarrow>  (sNorm2 v = 1))"

end (* of class axLightMinus *)


class AxLightMinus = axLightMinus +
  assumes AxLightMinus: "\<forall> m p v  . axLightMinus m p v"
begin
end (* of class AxLightMinus *)

end (* of theory AxLightMinus *)

