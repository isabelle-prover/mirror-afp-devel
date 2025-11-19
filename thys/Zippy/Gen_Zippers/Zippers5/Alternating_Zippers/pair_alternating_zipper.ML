(*  Title:    Zippy/pair_alternating_zipper.ML
    Auor:     Kevin Kappelmann
*)
signature \<^eval>\<open>mk_name ["PAIR", pfx_sfx_nargs "ALTERNATING_ZIPPER_ALTERNATING_DEP_ZIPPER"]\<close> =
sig
  structure SZ1 : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
  structure SZ2 : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_DEP_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} ZSub.Z{i}.ZM.Zip.dep =
    @{AllT_args} SZ1.ZSub.Z{i}.ZM.Zip.from * @{AllT_args} SZ1.ZSub.Z{i}.ZM.Zip.to
  where type @{AllT_args} ZSub.Z{i}.ZM.Unzip.dep =
    @{AllT_args} SZ1.ZSub.Z{i}.ZM.Unzip.from * @{AllT_args} SZ1.ZSub.Z{i}.ZM.Unzip.to
  where type @{AllT_args} ZSub.Z{i}.ZM.Up.dep =
    @{AllT_args} SZ1.ZSub.Z{i}.ZM.Up.from * @{AllT_args} SZ1.ZSub.Z{i}.ZM.Up.to
  where type @{AllT_args} ZSub.Z{i}.ZM.Down.dep =
    @{AllT_args} SZ1.ZSub.Z{i}.ZM.Down.from * @{AllT_args} SZ1.ZSub.Z{i}.ZM.Down.to
  where type @{AllT_args} ZSub.Z{i}.ZM.Left.dep =
    @{AllT_args} SZ1.ZSub.Z{i}.ZM.Left.from * @{AllT_args} SZ1.ZSub.Z{i}.ZM.Left.to
  where type @{AllT_args} ZSub.Z{i}.ZM.Right.dep =
    @{AllT_args} SZ1.ZSub.Z{i}.ZM.Right.from * @{AllT_args} SZ1.ZSub.Z{i}.ZM.Right.to
  where type @{AllT_args} ZSub.Down{i}.dep =
    @{AllT_args} SZ1.ZSub.Down{i}.from * @{AllT_args} SZ1.ZSub.Down{i}.to
  where type @{AllT_args} ZSub.Up{i}.dep =
    @{AllT_args} SZ1.ZSub.Up{i}.from * @{AllT_args} SZ1.ZSub.Up{i}.to\<close>\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  sharing type SZ2.SZ{i}.Zipper.container = SZ1.SZ{i}.Zipper.container
  sharing type SZ2.SZ{i}.Container.container = SZ1.SZ{i}.Container.container
  sharing type SZ2.SZ{i}.Content.container = SZ1.SZ{i}.Content.container
  sharing type SZ2.SZ{i}.ZCtxt.container = SZ1.SZ{i}.ZCtxt.container\<close>\<close>
  sharing type SZ2.ZSub.M.t = SZ1.ZSub.M.t

  include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} Z{i}.ZM.container =
    @{AllT_args} SZ1.ZSub.Z{i}.ZM.container * @{AllT_args} SZ2.ZSub.Z{i}.ZM.container
  where type @{AllT_args} Z{i}.ZD.content =
    @{AllT_args} SZ1.ZSub.Z{i}.ZD.content * @{AllT_args} SZ2.ZSub.Z{i}.ZD.content
  where type @{AllT_args} Z{i}.ZD.zcontext =
    @{AllT_args} SZ1.ZSub.Z{i}.ZD.zcontext * @{AllT_args} SZ2.ZSub.Z{i}.ZD.zcontext
  where type @{AllT_args} Z{i}.zipper =
    @{AllT_args} SZ1.ZSub.Z{i}.zipper * @{AllT_args} SZ2.ZSub.Z{i}.zipper\<close>\<close>
  sharing type M.t = SZ1.ZSub.M.t
end

functor \<^eval>\<open>mk_name ["Pair", pfx_sfx_nargs "Alternating_Zipper_Alternating_Dep_Zipper"]\<close>(
    structure AZ1 : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
    structure AZ2 : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_DEP_ZIPPER"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} Z{i}.ZM.Zip.dep =
      @{AllT_args} AZ1.Z{i}.ZM.Zip.from * @{AllT_args} AZ1.Z{i}.ZM.Zip.to
    where type @{AllT_args} Z{i}.ZM.Unzip.dep =
      @{AllT_args} AZ1.Z{i}.ZM.Unzip.from * @{AllT_args} AZ1.Z{i}.ZM.Unzip.to
    where type @{AllT_args} Z{i}.ZM.Up.dep =
      @{AllT_args} AZ1.Z{i}.ZM.Up.from * @{AllT_args} AZ1.Z{i}.ZM.Up.to
    where type @{AllT_args} Z{i}.ZM.Down.dep =
      @{AllT_args} AZ1.Z{i}.ZM.Down.from * @{AllT_args} AZ1.Z{i}.ZM.Down.to
    where type @{AllT_args} Z{i}.ZM.Left.dep =
      @{AllT_args} AZ1.Z{i}.ZM.Left.from * @{AllT_args} AZ1.Z{i}.ZM.Left.to
    where type @{AllT_args} Z{i}.ZM.Right.dep =
      @{AllT_args} AZ1.Z{i}.ZM.Right.from * @{AllT_args} AZ1.Z{i}.ZM.Right.to
    where type @{AllT_args} Down{i}.dep =
      @{AllT_args} AZ1.Down{i}.from * @{AllT_args} AZ1.Down{i}.to
    where type @{AllT_args} Up{i}.dep =
      @{AllT_args} AZ1.Up{i}.from * @{AllT_args} AZ1.Up{i}.to\<close>\<close>
    sharing type AZ2.M.t = AZ1.M.t
  ) :
    \<^eval>\<open>mk_name ["PAIR", pfx_sfx_nargs "ALTERNATING_ZIPPER_ALTERNATING_DEP_ZIPPER"]\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} SZ1.SZ{i}.Zipper.container =
      @{AllT_args} AZ1.Z{i}.zipper * @{AllT_args} AZ2.Z{i}.zipper
    where type @{AllT_args} SZ1.SZ{i}.Container.container =
      @{AllT_args} AZ1.Z{i}.ZM.container * @{AllT_args} AZ2.Z{i}.ZM.container
    where type @{AllT_args} SZ1.SZ{i}.Content.container =
      @{AllT_args} AZ1.Z{i}.ZD.content * @{AllT_args} AZ2.Z{i}.ZD.content
    where type @{AllT_args} SZ1.SZ{i}.ZCtxt.container =
      @{AllT_args} AZ1.Z{i}.ZD.zcontext * @{AllT_args} AZ2.Z{i}.ZD.zcontext\<close>\<close> =
struct
structure Z =
struct
  structure M : \<^eval>\<open>sfx_ParaT_nargs "MORPH_BASE"\<close> = AZ1
  open M
  structure L = AZ1.L
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Z{i} = \<^eval>\<open>sfx_T_nargs "Pair_Zipper_Dep_Zipper"\<close>(
    structure Z1 = AZ1.Z{i}
    structure Z2 = AZ2.Z{i})

  structure Down{i} = \<^eval>\<open>sfx_T_nargs "Pair_Morph_Dep_Morph"\<close>(
    structure M1 = AZ1.Down{i}
    structure M2 = AZ2.Down{i})

  structure Up{i} = \<^eval>\<open>sfx_T_nargs "Pair_Morph_Dep_Morph"\<close>(
    structure M1 = AZ1.Up{i}
    structure M2 = AZ2.Up{i})\<close>\<close>
end
open Z
structure SZ1 =
struct
  structure ZSub = AZ1
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure SZ{i} = Z{i}.SZ1\<close>\<close>
end
structure SZ2 =
struct
  structure ZSub = AZ2
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure SZ{i} = Z{i}.SZ2\<close>\<close>
end
end

signature \<^eval>\<open>mk_name ["PAIR", pfx_sfx_nargs "ALTERNATING_ZIPPER"]\<close> =
sig
  structure SZ1 : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
  structure SZ2 : \<^eval>\<open>pfx_sfx_nargs "SUB_ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  sharing type SZ2.SZ{i}.Zipper.container = SZ1.SZ{i}.Zipper.container
  sharing type SZ2.SZ{i}.Container.container = SZ1.SZ{i}.Container.container
  sharing type SZ2.SZ{i}.Content.container = SZ1.SZ{i}.Content.container
  sharing type SZ2.SZ{i}.ZCtxt.container = SZ1.SZ{i}.ZCtxt.container\<close>\<close>
  sharing type SZ2.ZSub.M.t = SZ1.ZSub.M.t

  include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} Z{i}.ZM.container =
    @{AllT_args} SZ1.ZSub.Z{i}.ZM.container * @{AllT_args} SZ2.ZSub.Z{i}.ZM.container
  where type @{AllT_args} Z{i}.ZD.content =
    @{AllT_args} SZ1.ZSub.Z{i}.ZD.content * @{AllT_args} SZ2.ZSub.Z{i}.ZD.content
  where type @{AllT_args} Z{i}.ZD.zcontext =
    @{AllT_args} SZ1.ZSub.Z{i}.ZD.zcontext * @{AllT_args} SZ2.ZSub.Z{i}.ZD.zcontext
  where type @{AllT_args} Z{i}.zipper =
    @{AllT_args} SZ1.ZSub.Z{i}.zipper * @{AllT_args} SZ2.ZSub.Z{i}.zipper\<close>\<close>
  sharing type M.t = SZ1.ZSub.M.t
end

functor \<^eval>\<open>mk_name ["Pair", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
    structure AZ1 : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
    structure AZ2 : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
    sharing type AZ2.M.t = AZ1.M.t
  ) :
    \<^eval>\<open>mk_name ["PAIR", pfx_sfx_nargs "ALTERNATING_ZIPPER"]\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} SZ1.SZ{i}.Zipper.container =
      @{AllT_args} AZ1.Z{i}.zipper * @{AllT_args} AZ2.Z{i}.zipper
    where type @{AllT_args} SZ1.SZ{i}.Container.container =
      @{AllT_args} AZ1.Z{i}.ZM.container * @{AllT_args} AZ2.Z{i}.ZM.container
    where type @{AllT_args} SZ1.SZ{i}.Content.container =
      @{AllT_args} AZ1.Z{i}.ZD.content * @{AllT_args} AZ2.Z{i}.ZD.content
    where type @{AllT_args} SZ1.SZ{i}.ZCtxt.container =
      @{AllT_args} AZ1.Z{i}.ZD.zcontext * @{AllT_args} AZ2.Z{i}.ZD.zcontext\<close>\<close> =
struct
structure PZ = \<^eval>\<open>mk_name ["Pair", pfx_sfx_nargs "Alternating_Zipper_Alternating_Dep_Zipper"]\<close>(
  structure AZ1 = AZ1
  structure AZ2 = \<^eval>\<open>pfx_sfx_nargs "Alternating_Dep_Zipper_Alternating_Zipper"\<close>(
    structure Z = AZ2
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    type @{AllT_args} dep{i}_zip = @{AllT_args} AZ1.Z{i}.ZM.Zip.from * @{AllT_args} AZ1.Z{i}.ZM.Zip.to
    type @{AllT_args} dep{i}_unzip = @{AllT_args} AZ1.Z{i}.ZM.Unzip.from * @{AllT_args} AZ1.Z{i}.ZM.Unzip.to
    type @{AllT_args} dep{i}_up = @{AllT_args} AZ1.Z{i}.ZM.Up.from * @{AllT_args} AZ1.Z{i}.ZM.Up.to
    type @{AllT_args} dep{i}_down = @{AllT_args} AZ1.Z{i}.ZM.Down.from * @{AllT_args} AZ1.Z{i}.ZM.Down.to
    type @{AllT_args} dep{i}_left = @{AllT_args} AZ1.Z{i}.ZM.Left.from * @{AllT_args} AZ1.Z{i}.ZM.Left.to
    type @{AllT_args} dep{i}_right = @{AllT_args} AZ1.Z{i}.ZM.Right.from * @{AllT_args} AZ1.Z{i}.ZM.Right.to
    type @{AllT_args} dep_down{i} = @{AllT_args} AZ1.Down{i}.from * @{AllT_args} AZ1.Down{i}.to
    type @{AllT_args} dep_up{i} = @{AllT_args} AZ1.Up{i}.from * @{AllT_args} AZ1.Up{i}.to\<close>\<close>))
open PZ
structure SZ2 =
struct open SZ2
structure ZSub = AZ2
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure SZ{i} = struct open SZ{i}; structure ZSub = AZ2.Z{i} end\<close>\<close>
end
end
