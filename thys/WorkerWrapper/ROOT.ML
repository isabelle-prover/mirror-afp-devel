tolerate_legacy_features := false;

no_document use_thys ["LList", "Maybe", "Nats"];

use_thys [
  "LFPFusion",
  "WorkerWrapper",
  "CounterExample",
  "WorkerWrapperNew",
  "Accumulator",
  "UnboxedNats",
  "Streams",
  "Continuations"];

no_document use_thys [
  "Backtracking",
  "Nub",
  "Last"
];
