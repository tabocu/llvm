#include "llvm/Pass.h"

#include "llvm/IR/IRBuilder.h"

#include <vector>

namespace llvm {

enum class LoopUnrollResult;

class AssumptionCache;
class DominatorTree;
class Loop;
class LoopInfo;
class OptimizationRemarkEmitter;
class ScalarEvolution;
class StoreInst;
class TargetTransformInfo;
class TargetLibraryInfo;

using StoreList = SmallVector<StoreInst*, 8>;

struct SLPAwareLoopUnrollPass : public FunctionPass {

  static char ID;
  SLPAwareLoopUnrollPass();

  bool runImpl(Function &F,
               LoopInfo *LI,
               ScalarEvolution *SE,
               DominatorTree *DT,
               AssumptionCache *AC,
               TargetTransformInfo *TTI,
               OptimizationRemarkEmitter *ORE,
               TargetLibraryInfo *TLI,
               IRBuilder<>& Builder);

  bool runOnFunction(Function &function) override;

  void getAnalysisUsage(AnalysisUsage &AU) const override;

private:
  int getEntryCost(TargetTransformInfo *TTI,
                   TargetLibraryInfo *TLI,
                   IRBuilder<> &Builder,
                   Value *V,
                   unsigned W);

  int costTree(TargetTransformInfo *TTI,
               TargetLibraryInfo *TLI,
               IRBuilder<> &Builder,
               Loop *L,
               StoreInst *SI,
               unsigned W);
};
}
