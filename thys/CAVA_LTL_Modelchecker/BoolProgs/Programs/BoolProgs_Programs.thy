theory BoolProgs_Programs
imports
  "BoolProgs_Philosophers"
  "BoolProgs_ReaderWriter"
  "BoolProgs_Simple"
  "BoolProgs_LeaderFilters"
  "~~/src/HOL/Library/List_lexord"
  "~~/src/HOL/Library/Char_ord"
begin

definition progs :: "(string, string \<times> string \<times> (nat \<Rightarrow> (bprog \<times> config) \<times> const_map \<times> fun_map)) mapping"
where "progs =  mapping_from_list [
                (''RW'', (''Reader/Writer'', ''# Readers and # Writers'', \<lambda>n. (reader_writer n n, rw_const n, rw_fun n))),
                (''S'', (''Simple Variable Setting'', ''# Variables'', \<lambda>n. (simple n, simple_const n, simple_fun n))),
                (''P'', (''Dining Philosophers'', ''# Philosophers'', \<lambda>n. (philosophers n, phil_const n, phil_fun n))),
                (''LF'', (''Leader Filters'', ''# Processes'', \<lambda>n. (leader_filters n, lf_const n, lf_fun n)))
              ]"

(* ensure this is an actual key *)
definition "default_prog \<equiv> ''S''"
definition keys_of_map :: "(string, 'a) mapping \<Rightarrow> string list" where
  "keys_of_map \<equiv> Mapping.ordered_keys"

definition chose_prog :: "string \<Rightarrow> nat \<Rightarrow> string \<times> string \<times> (bprog \<times> config) \<times> const_map \<times> fun_map"
where "chose_prog P n = (case Mapping.lookup progs P of 
                          Some (descr, ndescr, p) \<Rightarrow> (descr, ndescr, p n) 
                        | None \<Rightarrow> let (descr, ndescr, p) = the (Mapping.lookup progs default_prog)
                                 in (descr@'' (fallback)'', ndescr, p n))"

definition list_progs :: "(string \<times> string \<times> string) list" where
  "list_progs \<equiv> let keys = keys_of_map progs in
                map (\<lambda>k. let (descr, ndescr, p) = the (Mapping.lookup progs k)
                         in (k, descr, ndescr)) keys"
end
