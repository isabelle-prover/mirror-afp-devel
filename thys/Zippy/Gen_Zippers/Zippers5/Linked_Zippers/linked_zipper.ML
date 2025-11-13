(*  Title:      Zippy/linked_zipper.ML
    Author:     Kevin Kappelmann
*)
\<^imap>\<open>\<open>{i}\<close> => \<open>
signature \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "LINKED_DEP_ZIPPER"]\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  structure L : \<^eval>\<open>sfx_ParaT_nargs "SLENS"\<close>

  \<^imap>\<open>\<open>{j}\<close> => \<open>
  structure Z{j} : \<^eval>\<open>sfx_T_nargs "DEP_ZIPPER"\<close>
  sharing type Z{j}.M.t = M.t\<close>
  stop: {i}\<close>

  \<^imap>\<open>\<open>{j}\<close> => \<open>
  structure Down{j} : \<^eval>\<open>sfx_T_nargs "DEP_MORPH"\<close>
  sharing type Down{j}.from = Z{j}.zipper
  sharing type Down{j}.to = Z\<^eval>\<open>string_of_int ({j} + 1) ^ "."\<close>zipper
  sharing type Down{j}.M.t = M.t\<close>
  stop: \<open>{i} - 1\<close>\<close>

  \<^imap>\<open>\<open>{j}\<close> => \<open>
  structure Up{j} : \<^eval>\<open>sfx_T_nargs "DEP_MORPH"\<close>
  sharing type Up{j}.from = Z{j}.zipper
  sharing type Up{j}.to =  Z\<^eval>\<open>string_of_int ({j} - 1) ^ "."\<close>zipper
  sharing type Up{j}.M.t = M.t\<close>
  start: 2 stop: {i}\<close>
end

functor \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "Linked_Dep_Zipper"]\<close>(
    structure Z : \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "LINKED_DEP_ZIPPER_MORPHS"]\<close>
    \<^imap>\<open>\<open>{j}\<close> => \<open>
    structure ZD{j} : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    sharing type ZD{j}.zipper = Z.Z{j}.zipper\<close>
    stop: {i}\<close>
  ) : \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "LINKED_DEP_ZIPPER"]\<close> =
struct
open Z
structure L = \<^eval>\<open>sfx_ParaT_nargs "SLens"\<close>
\<^imap>\<open>\<open>{j}\<close> => \<open>
structure Z{j} = \<^eval>\<open>sfx_T_nargs "Dep_Zipper"\<close>(structure ZM = Z.Z{j}; structure ZD = ZD{j})\<close>
stop: {i}\<close>
end\<close>
start: 2\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
signature \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "LINKED_ZIPPER"]\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close>
  structure L : \<^eval>\<open>sfx_ParaT_nargs "SLENS"\<close>

  \<^imap>\<open>\<open>{j}\<close> => \<open>
  structure Z{j} : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  sharing type Z{j}.M.t = M.t\<close>
  stop: {i}\<close>

  \<^imap>\<open>\<open>{j}\<close> => \<open>
  structure Down{j} : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  sharing type Down{j}.from = Z{j}.zipper
  sharing type Down{j}.to = Z\<^eval>\<open>string_of_int ({j} + 1) ^ "."\<close>zipper
  sharing type Down{j}.M.t = M.t\<close>
  stop: \<open>{i} - 1\<close>\<close>

  \<^imap>\<open>\<open>{j}\<close> => \<open>
  structure Up{j} : \<^eval>\<open>sfx_T_nargs "MORPH"\<close>
  sharing type Up{j}.from = Z{j}.zipper
  sharing type Up{j}.to =  Z\<^eval>\<open>string_of_int ({j} - 1) ^ "."\<close>zipper
  sharing type Up{j}.M.t = M.t\<close>
  start: 2 stop: {i}\<close>
end\<close>
start: 2\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
functor \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "Linked_Dep_Zipper_Linked_Zipper"]\<close>(
    structure Z : \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "LINKED_ZIPPER"]\<close>
    \<^imap>\<open>\<open>{j}\<close> => \<open>
    type @{AllT_args} dep{j}_zip
    type @{AllT_args} dep{j}_unzip
    type @{AllT_args} dep{j}_up
    type @{AllT_args} dep{j}_down
    type @{AllT_args} dep{j}_left
    type @{AllT_args} dep{j}_right\<close>
    stop: {i}\<close>
    \<^imap>\<open>\<open>{j}\<close> => \<open>
    type @{AllT_args} dep_down{j}\<close>
    stop: \<open>{i} - 1\<close>\<close>
    \<^imap>\<open>\<open>{j}\<close> => \<open>
    type @{AllT_args} dep_up{j}\<close>
    start: 2 stop: {i}\<close>
  ) :
    \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "LINKED_DEP_ZIPPER"]\<close>
    \<^imap>\<open>\<open>{j}\<close> => \<open>
    where type @{AllT_args} Z{j}.ZM.Zip.dep = @{AllT_args} dep{j}_zip
    where type @{AllT_args} Z{j}.ZM.Unzip.dep = @{AllT_args} dep{j}_unzip
    where type @{AllT_args} Z{j}.ZM.Up.dep = @{AllT_args} dep{j}_up
    where type @{AllT_args} Z{j}.ZM.Down.dep = @{AllT_args} dep{j}_down
    where type @{AllT_args} Z{j}.ZM.Left.dep = @{AllT_args} dep{j}_left
    where type @{AllT_args} Z{j}.ZM.Right.dep = @{AllT_args} dep{j}_right\<close>
    stop: {i}\<close>
    \<^imap>\<open>\<open>{j}\<close> => \<open>
    where type @{AllT_args} Down{j}.dep = @{AllT_args} dep_down{j}\<close>
    stop: \<open>{i} - 1\<close>\<close>
    \<^imap>\<open>\<open>{j}\<close> => \<open>
    where type @{AllT_args} Up{j}.dep = @{AllT_args} dep_up{j}\<close>
    start: 2 stop: {i}\<close> =
struct
open Z
\<^imap>\<open>\<open>{j}\<close> => \<open>
structure Z{j} = \<^eval>\<open>sfx_T_nargs "Dep_Zipper_Zipper"\<close>(
  structure Z = Z{j};
  type @{AllT_args} dep_zip = @{AllT_args} dep{j}_zip
  type @{AllT_args} dep_unzip = @{AllT_args} dep{j}_unzip
  type @{AllT_args} dep_up = @{AllT_args} dep{j}_up
  type @{AllT_args} dep_down = @{AllT_args} dep{j}_down
  type @{AllT_args} dep_left = @{AllT_args} dep{j}_left
  type @{AllT_args} dep_right = @{AllT_args} dep{j}_right)\<close>
stop: {i}\<close>
\<^imap>\<open>\<open>{j}\<close> => \<open>
structure Down{j} = \<^eval>\<open>sfx_T_nargs "Dep_Morph_Morph"\<close>(
  structure M = Down{j}; type @{AllT_args} dep = @{AllT_args} dep_down{j})\<close>
stop: \<open>{i} - 1\<close>\<close>
\<^imap>\<open>\<open>{j}\<close> => \<open>
structure Up{j} = \<^eval>\<open>sfx_T_nargs "Dep_Morph_Morph"\<close>(
  structure M = Up{j}; type @{AllT_args} dep = @{AllT_args} dep_up{j})\<close>
start: 2 stop: {i}\<close>
end\<close>
start: 2\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
functor \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "Linked_Zipper_Linked_Dep_Zipper"]\<close>(
    Z : \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "LINKED_DEP_ZIPPER"]\<close>
    \<^imap>\<open>\<open>{j}\<close> => \<open>
    where type @{AllT_args} Z{j}.ZM.Zip.dep = unit
    where type @{AllT_args} Z{j}.ZM.Unzip.dep = unit
    where type @{AllT_args} Z{j}.ZM.Up.dep = unit
    where type @{AllT_args} Z{j}.ZM.Down.dep = unit
    where type @{AllT_args} Z{j}.ZM.Left.dep = unit
    where type @{AllT_args} Z{j}.ZM.Right.dep = unit\<close>
    stop: {i}\<close>
    \<^imap>\<open>\<open>{j}\<close> => \<open>
    where type @{AllT_args} Down{j}.dep = unit\<close>
    stop: \<open>{i} - 1\<close>\<close>
    \<^imap>\<open>\<open>{j}\<close> => \<open>
    where type @{AllT_args} Up{j}.dep = unit\<close>
    start: 2 stop: {i}\<close>
  ) : \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "LINKED_ZIPPER"]\<close> =
struct
open Z
\<^imap>\<open>\<open>{j}\<close> => \<open>
structure Z{j} = \<^eval>\<open>sfx_T_nargs "Zipper_Dep_Zipper"\<close>(Z{j})\<close>
stop: {i}\<close>
\<^imap>\<open>\<open>{j}\<close> => \<open>
structure Down{j} = \<^eval>\<open>sfx_T_nargs "Morph_Dep_Morph"\<close>(Down{j})\<close>
stop: \<open>{i} - 1\<close>\<close>
\<^imap>\<open>\<open>{j}\<close> => \<open>
structure Up{j} = \<^eval>\<open>sfx_T_nargs "Morph_Dep_Morph"\<close>(Up{j})\<close>
start: 2 stop: {i}\<close>
end\<close>
start: 2\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
functor \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "Linked_Zipper"]\<close>(
    structure Z : \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "LINKED_ZIPPER_MORPHS"]\<close>
    \<^imap>\<open>\<open>{j}\<close> => \<open>
    structure ZD{j} : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
    sharing type ZD{j}.zipper = Z.Z{j}.zipper\<close>
    stop: {i}\<close>
  ) : \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "LINKED_ZIPPER"]\<close> =
\<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "Linked_Zipper_Linked_Dep_Zipper"]\<close>(
  \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "Linked_Dep_Zipper"]\<close>(
  structure Z = \<^eval>\<open>mk_name [ML_Gen.nprefix "{i}", sfx_T_nargs "Linked_Dep_Zipper_Morphs_Linked_Zipper_Morphs"]\<close>(
    structure Z = Z
    \<^imap>\<open>\<open>{j}\<close> => \<open>
    type @{AllT_args} dep{j}_zip = unit
    type @{AllT_args} dep{j}_unzip = unit
    type @{AllT_args} dep{j}_up = unit
    type @{AllT_args} dep{j}_down = unit
    type @{AllT_args} dep{j}_left = unit
    type @{AllT_args} dep{j}_right = unit\<close>
    stop: {i}\<close>
    \<^imap>\<open>\<open>{j}\<close> => \<open>
    type @{AllT_args} dep_down{j} = unit\<close>
    stop: \<open>{i} - 1\<close>\<close>
    \<^imap>\<open>\<open>{j}\<close> => \<open>
    type @{AllT_args} dep_up{j} = unit\<close>
    start: 2 stop: {i}\<close>)
  \<^imap>\<open>\<open>{j}\<close> => \<open>
  structure ZD{j} = ZD{j}\<close>
  stop: {i}\<close>))\<close>
start: 2\<close>
