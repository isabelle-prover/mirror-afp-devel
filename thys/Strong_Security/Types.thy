(*
Title: Strong-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory Types
imports Main
begin

--"type parameters:"
--"'exp: expressions (arithmetic, boolean...)"
--"'val: values"
--"'id: identifier names"
--"'com: commands"
--"'d: domains"

text{* This is a collection of type synonyms. Note that not all of these type synonyms are 
  used within Strong-Security - some are used in WHATandWHERE-Security.*}

-- "type for memory states - map ids to values"
type_synonym ('id, 'val) State = "'id \<Rightarrow> 'val"

-- "type for evaluation functions mapping expressions to a values depending on a state"
type_synonym ('exp, 'id, 'val) Evalfunction = 
  "'exp \<Rightarrow> ('id, 'val) State \<Rightarrow> 'val"

-- "define configurations with threads as pair of commands and states"
type_synonym ('id, 'val, 'com) TConfig = "'com \<times> ('id, 'val) State"

-- "define configurations with thread pools as pair of command lists (thread pool) and states"
type_synonym ('id, 'val, 'com) TPConfig = 
  "('com list) \<times> ('id, 'val) State"

-- "type for program states (including the set of commands and a symbol for terminating - None)"
type_synonym 'com ProgramState = "'com option"

-- "type for configurations with program states"
type_synonym ('id, 'val, 'com) PSConfig = 
  "'com ProgramState \<times> ('id, 'val) State"

-- "type for labels with a list of spawned threads"
type_synonym 'com Label = "'com list"

-- "type for step relations from single commands to a program state, with a label"
type_synonym ('exp, 'id, 'val, 'com) TLSteps = "
  (('id, 'val, 'com) TConfig \<times> 'com Label 
    \<times> ('id, 'val, 'com) PSConfig) set"

-- "curried version of previously defined type"
type_synonym ('exp, 'id, 'val, 'com) TLSteps_curry =
"'com \<Rightarrow> ('id, 'val) State \<Rightarrow> 'com Label \<Rightarrow> 'com ProgramState 
  \<Rightarrow> ('id, 'val) State \<Rightarrow> bool"

-- "type for step relations from thread pools to thread pools"
type_synonym ('exp, 'id, 'val, 'com) TPSteps = "
  (('id, 'val, 'com) TPConfig \<times> ('id, 'val, 'com) TPConfig) set"

-- "curried version of previously defined type"
type_synonym ('exp, 'id, 'val, 'com) TPSteps_curry =
"'com list \<Rightarrow> ('id, 'val) State \<Rightarrow> 'com list \<Rightarrow> ('id, 'val) State \<Rightarrow> bool"

-- "define type of step relations for single threads to thread pools"
type_synonym ('exp, 'id, 'val, 'com) TSteps = 
  "(('id, 'val, 'com) TConfig \<times> ('id, 'val, 'com) TPConfig) set"

-- "define the same type as TSteps, but in a curried version (allowing syntax abbreviations)"
type_synonym ('exp, 'id, 'val, 'com) TSteps_curry =
"'com \<Rightarrow> ('id, 'val) State \<Rightarrow> 'com list \<Rightarrow> ('id, 'val) State \<Rightarrow> bool"

-- "type for simple domain assignments; 'd has to be an instance of order (partial order"
type_synonym ('id, 'd) DomainAssignment = "'id \<Rightarrow> 'd::order"

type_synonym 'com Bisimulation_type = "(('com list) \<times> ('com list)) set"

--"type for escape hatches"
type_synonym ('d, 'exp) Hatch = "'d \<times> 'exp"

--"type for sets of escape hatches"
type_synonym ('d, 'exp) Hatches = "(('d, 'exp) Hatch) set"

--"type for local escape hatches"
type_synonym ('d, 'exp) lHatch = "'d \<times> 'exp \<times> nat"

--"type for sets of local escape hatches"
type_synonym ('d, 'exp) lHatches = "(('d, 'exp) lHatch) set"


end
