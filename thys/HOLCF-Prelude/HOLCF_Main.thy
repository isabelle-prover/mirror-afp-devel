section \<open>Initial Setup for HOLCF-Prelude\<close>

theory HOLCF_Main
  imports
    HOLCF
    "HOLCF-Library.Int_Discrete"
    "HOL-Library.Adhoc_Overloading"
begin

text \<open>
  All theories from the Isabelle distribution which are used
  anywhere in the HOLCF-Prelude library must be imported via this file.
  This way, we only have to hide constant names and syntax in one place.
\<close>

hide_type (open) list

hide_const (open)
  List.append List.concat List.Cons List.distinct List.filter List.last
  List.foldr List.foldl List.length List.lists List.map List.Nil List.nth
  List.partition List.replicate List.set List.take List.upto List.zip
  Orderings.less Product_Type.fst Product_Type.snd

no_notation Map.map_add (infixl \<open>++\<close> 100)

no_notation List.upto (\<open>(1[_../_])\<close>)

no_notation
  Rings.divide (infixl \<open>div\<close> 70) and
  Rings.modulo (infixl \<open>mod\<close> 70)

no_notation
  Set.member  (\<open>(:)\<close>) and
  Set.member  (\<open>(\<open>notation=\<open>infix :\<close>\<close>_/ : _)\<close> [51, 51] 50)

no_translations
  "[x, xs]" == "x # [xs]"
  "[x]" == "x # []"

unbundle no list_enumeration_syntax

no_notation
  List.Nil (\<open>[]\<close>)

no_syntax "_bracket" :: "types \<Rightarrow> type \<Rightarrow> type" (\<open>(\<open>notation=\<open>infix =>\<close>\<close>[_]/ => _)\<close> [0, 0] 0)
no_syntax "_bracket" :: "types \<Rightarrow> type \<Rightarrow> type" (\<open>(\<open>notation=\<open>infix \<Rightarrow>\<close>\<close>[_]/ \<Rightarrow> _)\<close> [0, 0] 0)

no_translations
  "[x<-xs . P]" == "CONST List.filter (%x. P) xs"

no_syntax (ASCII)
  "_filter" :: "pttrn \<Rightarrow> 'a List.list \<Rightarrow> bool \<Rightarrow> 'a List.list"  (\<open>(\<open>indent=1 notation=\<open>mixfix filter\<close>\<close>[_<-_./ _])\<close>)
no_syntax
  "_filter" :: "pttrn \<Rightarrow> 'a List.list \<Rightarrow> bool \<Rightarrow> 'a List.list"  (\<open>(\<open>indent=1 notation=\<open>mixfix filter\<close>\<close>[_\<leftarrow>_ ./ _])\<close>)

text \<open>Declarations that belong in HOLCF/Tr.thy:\<close>

declare trE [cases type: tr]
declare tr_induct [induct type: tr]

end
