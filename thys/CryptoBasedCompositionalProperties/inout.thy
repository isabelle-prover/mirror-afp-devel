(*
   Title: Theory  inout.thy
   Author:    Maria Spichkova <maria.spichkova at rmit.edu.au>, 2014
*)
 
section {*Correctness of the relations between sets of Input/Output channels*}
 
theory  inout 
imports Secrecy_types
begin

consts 
  subcomponents ::  "specID \<Rightarrow> specID set"

-- "Mappings, defining sets of input, local, and output channels"
-- "of a component"
consts
  ins :: "specID \<Rightarrow> chanID set"
  loc :: "specID \<Rightarrow> chanID set"
  out :: "specID \<Rightarrow> chanID set"

-- "Predicate insuring the correct mapping from the component identifier"
-- "to the set of input channels of a component"
definition
  inStream :: "specID \<Rightarrow> chanID set \<Rightarrow> bool"
where
  "inStream x y  \<equiv> (ins x = y)"

-- "Predicate insuring the correct mapping from the component identifier"
-- "to the set of local channels of a component"
definition
  locStream :: "specID \<Rightarrow> chanID set \<Rightarrow> bool"
where
  "locStream x y \<equiv> (loc x = y)"

-- "Predicate insuring the correct mapping from the component identifier"
-- "to the set of output channels of a component"
definition
  outStream :: "specID \<Rightarrow> chanID set \<Rightarrow> bool"
where
  "outStream x y \<equiv> (out x = y)"

-- "Predicate insuring the correct relations between"
-- "to the set of input, output and local channels of a component"
definition
  correctInOutLoc :: "specID \<Rightarrow> bool"
where
  "correctInOutLoc x \<equiv> 
   (ins x) \<inter> (out x) = {} 
    \<and> (ins x) \<inter> (loc x) = {} 
    \<and> (loc x) \<inter> (out x) = {} " 

-- "Predicate insuring the correct relations between"
-- "sets of input channels within a composed component"
definition
  correctCompositionIn :: "specID \<Rightarrow> bool"
where
  "correctCompositionIn x \<equiv> 
  (ins x) = (\<Union> (ins ` (subcomponents x)) - (loc x))
  \<and> (ins x) \<inter> (\<Union> (out ` (subcomponents x))) = {}" 

-- "Predicate insuring the correct relations between"
-- "sets of output channels within a composed component"
definition
  correctCompositionOut :: "specID \<Rightarrow> bool"
where
  "correctCompositionOut x \<equiv> 
  (out x) = (\<Union> (out ` (subcomponents x))- (loc x))
  \<and> (out x) \<inter> (\<Union> (ins ` (subcomponents x))) = {} " 

-- "Predicate insuring the correct relations between"
-- "sets of local channels within a composed component"
definition
  correctCompositionLoc :: "specID \<Rightarrow> bool"
where
  "correctCompositionLoc x \<equiv> 
   (loc x) = \<Union> (ins ` (subcomponents x))
           \<inter> \<Union> (out ` (subcomponents x))" 

-- "If a component is an elementary one (has no subcomponents)"
-- "its set of local channels should be empty"
lemma subcomponents_loc:
assumes "correctCompositionLoc x"
       and "subcomponents x = {}"
shows "loc x = {}"
using assms by (simp add: correctCompositionLoc_def)

end