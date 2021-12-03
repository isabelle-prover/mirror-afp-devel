(*
  File: auto2_setup.ML
  Author: Kevin Kappelmann

  Setup for auto2
*)

signature AUTO2_SETUP =
sig
  structure Auto2_Keywords: AUTO2_KEYWORDS
  structure UtilBase: UTIL_BASE
  structure UtilLogic : UTIL_LOGIC
  structure Basic_UtilLogic : BASIC_UTIL_LOGIC
  structure WfTerm: WFTERM
  structure RewriteTable: REWRITE_TABLE
  structure PropertyData: PROPERTY_DATA
  structure Matcher: MATCHER
  structure BoxItem: BOXITEM
  structure ItemIO: ITEM_IO
  structure WellformData: WELLFORM_DATA
  structure Auto2Data: AUTO2_DATA
  structure Update: UPDATE
  structure Status: STATUS
  structure Normalizer: NORMALIZER
  structure ProofStep: PROOFSTEP
  structure ProofStepData: PROOFSTEP_DATA
  structure Logic_ProofSteps: LOGIC_PROOFSTEPS
  structure ProofStatus: PROOFSTATUS
  structure Auto2: AUTO2
  structure Auto2_Outer: AUTO2_OUTER
end

functor Auto2_Setup(
  structure Auto2_Keywords: AUTO2_KEYWORDS;
  structure UtilBase: UTIL_BASE;
  ) : AUTO2_SETUP =
struct

structure Auto2_Keywords = Auto2_Keywords
structure UtilBase = UtilBase
structure UtilLogic = UtilLogic(UtilBase)
structure Basic_UtilLogic: BASIC_UTIL_LOGIC = UtilLogic
structure Property = Property(
  structure Basic_UtilBase = UtilBase;
  structure UtilLogic = UtilLogic;
)
structure WfTerm = WfTerm(
  structure Basic_UtilBase = UtilBase;
  structure UtilLogic = UtilLogic;
)
structure RewriteTable = RewriteTable(UtilLogic)
structure PropertyData = PropertyData(
  structure Basic_UtilBase = UtilBase;
  structure Property = Property;
  structure RewriteTable =RewriteTable;
  structure UtilLogic = UtilLogic;
)
structure Matcher = Matcher(RewriteTable)
structure BoxItem = BoxItem(UtilBase)
structure ItemIO = ItemIO(
  structure Matcher = Matcher;
  structure Property = Property;
  structure PropertyData = PropertyData;
  structure RewriteTable = RewriteTable;
  structure UtilBase = UtilBase;
  structure UtilLogic = UtilLogic;
)
structure WellformData = WellformData(
  structure Basic_UtilBase = UtilBase;
  structure Basic_UtilLogic = Basic_UtilLogic;
  structure ItemIO = ItemIO;
  structure Property = Property;
  structure PropertyData = PropertyData;
  structure RewriteTable = RewriteTable;
  structure WfTerm = WfTerm;
)
structure Auto2Data = Auto2Data(
  structure PropertyData = PropertyData;
  structure RewriteTable = RewriteTable;
  structure WellformData = WellformData;
)
structure Update = Update(
  structure BoxItem = BoxItem;
  structure ItemIO = ItemIO;
  structure UtilLogic = UtilLogic;
)
structure Status = Status(
  structure BoxItem = BoxItem;
  structure ItemIO = ItemIO;
  structure UtilLogic = UtilLogic
  structure PropertyData = PropertyData;
  structure RewriteTable = RewriteTable;
  structure WellformData = WellformData;
)
val _ = Theory.setup (ItemIO.add_basic_item_io)
structure Normalizer = Normalizer(
  structure BoxItem = BoxItem;
  structure UtilBase = UtilBase;
  structure UtilLogic = UtilLogic;
  structure Update = Update;
)
structure ProofStep = ProofStep(
  structure ItemIO = ItemIO;
  structure Matcher = Matcher;
  structure PropertyData = PropertyData;
  structure RewriteTable = RewriteTable;
  structure UtilBase = UtilBase;
  structure UtilLogic = UtilLogic;
  structure Update = Update;
  structure WellformData = WellformData;
)
structure ProofStepData = ProofStepData(
  structure ItemIO = ItemIO;
  structure Normalizer = Normalizer;
  structure ProofStep = ProofStep;
  structure Property = Property;
  structure UtilBase = UtilBase;
  structure UtilLogic = UtilLogic;
)
structure Logic_ProofSteps = Logic_ProofSteps(
  structure BoxItem = BoxItem;
  structure ItemIO = ItemIO;
  structure Matcher = Matcher;
  structure Normalizer = Normalizer;
  structure Property = Property;
  structure ProofStepData = ProofStepData;
  structure RewriteTable = RewriteTable;
  structure UtilBase = UtilBase;
  structure UtilLogic = UtilLogic;
  structure Update = Update;
)
val _ = Theory.setup Logic_ProofSteps.add_logic_proofsteps
val _ = Theory.setup Logic_ProofSteps.add_disj_proofsteps
val _ = Theory.setup Logic_ProofSteps.add_disj_normalizers
structure ProofStatus = ProofStatus(
  structure Auto2Data = Auto2Data;
  structure BoxItem = BoxItem;
  structure ItemIO = ItemIO;
  structure Normalizer = Normalizer;
  structure Logic_ProofSteps = Logic_ProofSteps;
  structure Property = Property;
  structure PropertyData = PropertyData;
  structure ProofStepData = ProofStepData;
  structure RewriteTable = RewriteTable;
  structure Status = Status;
  structure UtilBase = UtilBase;
  structure UtilLogic = UtilLogic;
  structure Update = Update;
  structure WellformData = WellformData;
)
structure Auto2 = Auto2(
  structure ProofStatus = ProofStatus;
  structure Status = Status;
  structure UtilLogic = UtilLogic;
)
structure Auto2_Outer = Auto2_Outer(
  structure Auto2 = Auto2;
  structure Auto2_Keywords = Auto2_Keywords;
  structure UtilBase = UtilBase;
  structure UtilLogic = UtilLogic;
)

end