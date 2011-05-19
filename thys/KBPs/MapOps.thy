(* Title: Map abstraction.
   Author: Peter Gammie < peteg42 at gmail dot com >
*)

header "Map operations"

theory MapOps
imports Main
begin

text{*

We need concrete algorithms to maintain the various maps. Here
we abstract their API a little bit. Framed this way as the code
generator does not understand locales.

*}

(* FIXME: have a domain of definition to ease the data refinement. *)

record ('m, 'k, 'e) MapOps =
  empty :: "'m"
  lookup :: "'m \<Rightarrow> 'k \<rightharpoonup> 'e"
  update :: "'k \<Rightarrow> 'e \<Rightarrow> 'm \<Rightarrow> 'm"

definition
  MapOps :: "('k \<Rightarrow> 'kabs) \<Rightarrow> 'kabs set \<Rightarrow> ('m, 'k, 'e) MapOps \<Rightarrow> bool"
where
  "MapOps \<alpha> d ops \<equiv>
      (\<forall>k. \<alpha> k \<in> d \<longrightarrow> lookup ops (empty ops) k = None)
    \<and> (\<forall>e k k' M. \<alpha> k \<in> d \<and> \<alpha> k' \<in> d
        \<longrightarrow> lookup ops (update ops k e M) k'
          = (if \<alpha> k' = \<alpha> k then Some e else lookup ops M k'))"



lemma MapOpsI[intro]:
  "\<lbrakk> \<And>k. \<alpha> k \<in> d \<Longrightarrow> lookup ops (empty ops) k = None;
     \<And>e k k' M. \<lbrakk> \<alpha> k \<in> d; \<alpha> k' \<in> d \<rbrakk> \<Longrightarrow>
                 lookup ops (update ops k e M) k'
              = (if \<alpha> k' = \<alpha> k then Some e else lookup ops M k') \<rbrakk>
     \<Longrightarrow> MapOps \<alpha> d ops"
  unfolding MapOps_def by blast

lemma MapOps_emptyD:
  "\<lbrakk> \<alpha> k \<in> d; MapOps \<alpha> d ops \<rbrakk> \<Longrightarrow> lookup ops (empty ops) k = None"
  unfolding MapOps_def by simp

lemma MapOps_lookup_updateD:
  "\<lbrakk> \<alpha> k \<in> d; \<alpha> k' \<in> d; MapOps \<alpha> d ops \<rbrakk> \<Longrightarrow> lookup ops (update ops k e M) k' = (if \<alpha> k' = \<alpha> k then Some e else lookup ops M k')"
  unfolding MapOps_def by simp



text{* Useful for fudging a set-membership operation. *}

definition
  "isSome opt \<equiv> case opt of None \<Rightarrow> False | Some _ \<Rightarrow> True"


lemma isSome_simps[simp]:
  "\<And>x. isSome (Some x)"
  "\<And>x. \<not> isSome x \<longleftrightarrow> x = None"
  unfolding isSome_def by (auto split: option.split)

lemma isSome_eq:
  "isSome x \<longleftrightarrow> (\<exists>y. x = Some y)"
  unfolding isSome_def by (auto split: option.split)

lemma isSomeE: "\<lbrakk> isSome x; \<And>s. x = Some s \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  unfolding isSome_def by (cases x) auto




end

