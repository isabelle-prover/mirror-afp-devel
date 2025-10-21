use "src/isalib/build.sml";
use "src/util/build.sml";
use "src/serialization/build.sml";
use "src/errors/build.sml";
use "src/dbm/build.sml";
use "src/parsing/build.sml";
use "src/product_construction/build.sml";
use "src/smlnjlib/build.sml";
use "src/worklist_algorithms/build.sml";
use "src/model_checking/build.sml";
Build.subdir "src/"
             [
                        "compress",
                        "certification",
                        "mlunta",
                        "checker"
             ]
