(*  Title:      Zippy/zippy_goals_results_top_meta_vars_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_GOALS_RESULTS_TOP_META_VARS_MIXIN_BASE =
sig
  include ZIPPY_GOALS_RESULTS_MIXIN_BASE
  structure Top_Meta_Vars : ZIPPY_TOP_META_VARS_MIXIN_BASE
  sharing type Top_Meta_Vars.L.container = GCluster.L.container
end

functor Zippy_Goals_Results_Top_Meta_Vars_Mixin_Base(A :
  sig
    include ZIPPY_GOALS_RESULTS_MIXIN_BASE
    structure Top_Meta_Vars : ZIPPY_TOP_META_VARS_MIXIN_BASE
    sharing type Top_Meta_Vars.L.container = GCluster.L.container
  end) : ZIPPY_GOALS_RESULTS_TOP_META_VARS_MIXIN_BASE
  = A
