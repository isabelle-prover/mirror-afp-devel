(*  Title:      Zippy/alternating_zipper_morphs.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_DEP_ZIPPER_MORPHS"\<close> =
sig
  include \<^eval>\<open>pfx_sfx_nargs "LINKED_DEP_ZIPPER_MORPHS"\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Down{i} : \<^eval>\<open>sfx_T_nargs "DEP_MORPH"\<close>
  sharing type Down{i}.from = Z{i}.zipper
  sharing type Down{i}.to = Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>zipper
  sharing type Down{i}.M.t = M.t\<close>
  start: \<open>ML_Gen.nzippers ()\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Up{i} : \<^eval>\<open>sfx_T_nargs "DEP_MORPH"\<close>
  sharing type Up{i}.from = Z{i}.zipper
  sharing type Up{i}.to = Z\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>zipper
  sharing type Up{i}.M.t = M.t\<close>
  stop: 1\<close>
end

signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_MORPHS"\<close> =
sig
  include \<^eval>\<open>pfx_sfx_nargs "LINKED_ZIPPER_MORPHS"\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Down{i} : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  sharing type Down{i}.from = Z{i}.zipper
  sharing type Down{i}.to = Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>zipper
  sharing type Down{i}.M.t = M.t\<close>
  start: \<open>ML_Gen.nzippers ()\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Up{i} : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  sharing type Up{i}.from = Z{i}.zipper
  sharing type Up{i}.to = Z\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>zipper
  sharing type Up{i}.M.t = M.t\<close>
  stop: 1\<close>
end

functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Dep_Zipper_Morphs_Alternating_Zipper_Morphs"\<close>(
    structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_MORPHS"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    type @{AllT_args} dep{i}_zip
    type @{AllT_args} dep{i}_unzip
    type @{AllT_args} dep{i}_up
    type @{AllT_args} dep{i}_down
    type @{AllT_args} dep{i}_left
    type @{AllT_args} dep{i}_right
    type @{AllT_args} dep_down{i}
    type @{AllT_args} dep_up{i}\<close>\<close>
  ) :
    \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_DEP_ZIPPER_MORPHS"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} Z{i}.Zip.dep = @{AllT_args} dep{i}_zip
    where type @{AllT_args} Z{i}.Unzip.dep = @{AllT_args} dep{i}_unzip
    where type @{AllT_args} Z{i}.Up.dep = @{AllT_args} dep{i}_up
    where type @{AllT_args} Z{i}.Down.dep = @{AllT_args} dep{i}_down
    where type @{AllT_args} Z{i}.Left.dep = @{AllT_args} dep{i}_left
    where type @{AllT_args} Z{i}.Right.dep = @{AllT_args} dep{i}_right
    where type @{AllT_args} Down{i}.dep = @{AllT_args} dep_down{i}
    where type @{AllT_args} Up{i}.dep = @{AllT_args} dep_up{i}\<close>\<close> =
struct
open Z
structure Z = \<^eval>\<open>pfx_sfx_nargs "Linked_Dep_Zipper_Morphs_Linked_Zipper_Morphs"\<close>(
  structure Z = Z
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  type @{AllT_args} dep{i}_zip = @{AllT_args} dep{i}_zip
  type @{AllT_args} dep{i}_unzip = @{AllT_args} dep{i}_unzip
  type @{AllT_args} dep{i}_up = @{AllT_args} dep{i}_up
  type @{AllT_args} dep{i}_down = @{AllT_args} dep{i}_down
  type @{AllT_args} dep{i}_left = @{AllT_args} dep{i}_left
  type @{AllT_args} dep{i}_right = @{AllT_args} dep{i}_right
  type @{AllT_args} dep_down{i} = @{AllT_args} dep_down{i}
  type @{AllT_args} dep_up{i} = @{AllT_args} dep_up{i}\<close>\<close>)
open Z
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Down{i} = \<^eval>\<open>sfx_T_nargs "Dep_Morph_Morph"\<close>(
  structure M = Down{i}; type @{AllT_args} dep = @{AllT_args} dep_down{i})\<close>
start: \<open>ML_Gen.nzippers ()\<close>\<close>
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Up{i} = \<^eval>\<open>sfx_T_nargs "Dep_Morph_Morph"\<close>(
  structure M = Up{i}; type @{AllT_args} dep = @{AllT_args} dep_up{i})\<close>
stop: 1\<close>
end

functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Morphs_Alternating_Dep_Zipper_Morphs"\<close>(
    Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_DEP_ZIPPER_MORPHS"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} Z{i}.Zip.dep = unit
    where type @{AllT_args} Z{i}.Unzip.dep = unit
    where type @{AllT_args} Z{i}.Up.dep = unit
    where type @{AllT_args} Z{i}.Down.dep = unit
    where type @{AllT_args} Z{i}.Left.dep = unit
    where type @{AllT_args} Z{i}.Right.dep = unit
    where type @{AllT_args} Down{i}.dep = unit
    where type @{AllT_args} Up{i}.dep = unit\<close>\<close>
  ) : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_MORPHS"\<close> =
struct
open Z
structure Z = \<^eval>\<open>pfx_sfx_nargs "Linked_Zipper_Morphs_Linked_Dep_Zipper_Morphs"\<close>(Z)
open Z
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Down{i} = \<^eval>\<open>sfx_T_nargs "Morph_Dep_Morph"\<close>(Down{i})\<close>
start: \<open>ML_Gen.nzippers ()\<close>\<close>
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Up{i} = \<^eval>\<open>sfx_T_nargs "Morph_Dep_Morph"\<close>(Up{i})\<close>
stop: 1\<close>
end
