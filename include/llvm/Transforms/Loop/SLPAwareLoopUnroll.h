#include "llvm/Pass.h"

#include <vector>

namespace llvm {

enum class LoopUnrollResult;

class AssumptionCache;
class DominatorTree;
class Loop;
class LoopInfo;
class OptimizationRemarkEmitter;
class ScalarEvolution;
class TargetTransformInfo;

struct SLPAwareLoopUnrollPass : public FunctionPass {

  static char ID;
  SLPAwareLoopUnrollPass();

  bool runImpl(Function &F, LoopInfo &LI, ScalarEvolution &SE,
               DominatorTree &DT, AssumptionCache &AC,
               TargetTransformInfo &TTI, OptimizationRemarkEmitter &ORE);

  bool runOnFunction(Function &function) override;

  void getAnalysisUsage(AnalysisUsage &AU) const override;
};
}
